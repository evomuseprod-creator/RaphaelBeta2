"""
Filter mask sweep — replays Beta's 23 detected setups under all 16
combinations of the 4 directional filter toggles, with Bot.py risk geometry.
Reports the mask(s) with highest net pips.

All filter logic is taken verbatim from Raphaelbeta.py (no new logic).
"""

import csv
import os
from datetime import datetime, timedelta, timezone
from itertools import product
from pathlib import Path

import pandas as pd
from dotenv import load_dotenv
import oandapyV20
import oandapyV20.endpoints.instruments as instruments

PKG = Path(__file__).resolve().parent
load_dotenv(PKG / ".env")
oanda = oandapyV20.API(access_token=os.environ["OANDA_KEY"])

# Bot.py geometry
TP1_DIST, TP2_DIST, MAX_SL = 4.5, 9.5, 20.0

# Filter constants (from RaphaelBeta2.py)
H1_EMA_PERIOD  = 50
H1_NEUTRAL_PCT = 0.001

LOCAL_UTC_OFFSET = timedelta(hours=8)
START = datetime(2026, 5, 4, 0, 0, tzinfo=timezone.utc)
END   = datetime.now(timezone.utc) - timedelta(minutes=5)

BETA_LOG = Path("/Users/user/Desktop/RaphaelBeta/signals_log.csv")


def fetch_candles(from_dt, to_dt, granularity):
    out = []
    cursor = from_dt
    step = timedelta(hours=12 if granularity == "M1" else (24 if granularity == "M5" else 96))
    while cursor < to_dt:
        chunk_to = min(cursor + step, to_dt)
        params = {"granularity": granularity, "price": "M",
                  "from": cursor.isoformat().replace("+00:00", "Z"),
                  "to":   chunk_to.isoformat().replace("+00:00", "Z")}
        r = instruments.InstrumentsCandles("XAU_USD", params=params)
        oanda.request(r)
        cs = r.response["candles"]
        if not cs:
            cursor = chunk_to; continue
        for c in cs:
            out.append({
                "t": datetime.fromisoformat(c["time"].replace("Z", "+00:00")),
                "o": float(c["mid"]["o"]), "h": float(c["mid"]["h"]),
                "l": float(c["mid"]["l"]), "c": float(c["mid"]["c"]),
            })
        last_t = out[-1]["t"]
        if last_t <= cursor: break
        step_min = {"M1":1,"M5":5,"H1":60,"H4":240}[granularity]
        cursor = last_t + timedelta(minutes=step_min)
    return out


def load_setups():
    rows = []
    with open(BETA_LOG) as f:
        for r in csv.DictReader(f):
            if r["status"] != "OPEN": continue
            local_t = datetime.fromisoformat(r["time"])
            t = (local_t - LOCAL_UTC_OFFSET).replace(tzinfo=timezone.utc)
            if t < START: continue
            rows.append({"t": t, "dir": r["type"], "entry": float(r["entry"]),
                         "beta_sl_dist": float(r["sl_distance"])})
    return rows


def h1_bias_at(t, h1_df):
    """Compute EMA50 bias using H1 candles up to (but not including) t."""
    hist = h1_df[h1_df["t"] < t]
    if len(hist) < 5:
        return "NEUTRAL"
    closes = hist["c"].ewm(span=H1_EMA_PERIOD, adjust=False).mean()
    ema = closes.iloc[-1]
    h1_close = hist["c"].iloc[-1]
    pct = (h1_close - ema) / ema
    if pct > H1_NEUTRAL_PCT:  return "BULLISH"
    if pct < -H1_NEUTRAL_PCT: return "BEARISH"
    return "NEUTRAL"


def m5_entry_candle(t, m5_df):
    """The M5 candle covering time t (or the most recent one before)."""
    cand = m5_df[m5_df["t"] <= t]
    return cand.iloc[-1] if len(cand) else None


def m5_lookback_high(t, m5_df, n=20):
    cand = m5_df[m5_df["t"] <= t].tail(n)
    return cand["h"].max() if len(cand) else None


def last_h1_candle(t, h1_df):
    cand = h1_df[h1_df["t"] < t]
    return cand.iloc[-1] if len(cand) else None


def filters_for(setup, h1_df, m5_df):
    """Return dict of which filter blocks would reject this setup."""
    direction = setup["dir"]
    t = setup["t"]
    entry = setup["entry"]

    f1 = False  # SELL_BEARISH_CANDLE_BLOCK
    f2 = False  # SELL_H1_NEUTRAL_BLOCK
    f3 = False  # SELL_LONDON_BLOCK
    f4 = False  # BUY_BEAR_H1_NEAR_STRUCT_BLOCK

    h1b = h1_bias_at(t, h1_df)
    if direction == "SELL":
        # F2: H1 neutral block
        if h1b == "NEUTRAL":
            f2 = True
        # F3: London block (7-13 UTC)
        if 7 <= t.hour < 13:
            f3 = True
        # F1: bearish candle block
        m5c = m5_entry_candle(t, m5_df)
        if m5c is not None and m5c["c"] < m5c["o"]:
            f1 = True
    else:  # BUY
        # F4: H1 bearish + close to recent high
        h1c = last_h1_candle(t, h1_df)
        if h1c is not None and h1c["c"] < h1c["o"]:
            high20 = m5_lookback_high(t, m5_df, 20)
            if high20 is not None and (high20 - entry) < 8:
                f4 = True
    return {"f1": f1, "f2": f2, "f3": f3, "f4": f4, "h1b": h1b}


def resolve_trade(setup, m1):
    direction, entry = setup["dir"], setup["entry"]
    sl_dist = min(setup["beta_sl_dist"], MAX_SL)
    if direction == "BUY":
        sl, tp1, tp2 = entry - sl_dist, entry + TP1_DIST, entry + TP2_DIST
    else:
        sl, tp1, tp2 = entry + sl_dist, entry - TP1_DIST, entry - TP2_DIST

    tp1_hit = False; sl_now = sl
    for c in m1:
        if c["t"] <= setup["t"]: continue
        hi, lo = c["h"], c["l"]
        if direction == "BUY":
            sl_t, tp1_t, tp2_t = lo <= sl_now, hi >= tp1, hi >= tp2
        else:
            sl_t, tp1_t, tp2_t = hi >= sl_now, lo <= tp1, lo <= tp2
        if not tp1_hit:
            if sl_t: return "SL", -int(round(abs(entry - sl) * 10))
            if tp1_t:
                tp1_hit = True; sl_now = entry  # BE shift
                if tp2_t: return "TP2", int(round(TP2_DIST * 10))
                continue
        if direction == "BUY":
            be_t = lo <= sl_now
        else:
            be_t = hi >= sl_now
        if be_t and not tp2_t: return "BE", 0
        if tp2_t: return "TP2", int(round(TP2_DIST * 10))
        if be_t and tp2_t: return "BE", 0
    return "OPEN", 0


def main():
    print("Fetching candles...")
    m1_list = fetch_candles(START, END, "M1")
    m5_list = fetch_candles(START - timedelta(hours=2), END, "M5")
    h1_list = fetch_candles(START - timedelta(days=10), END, "H1")
    print(f"  M1={len(m1_list)} M5={len(m5_list)} H1={len(h1_list)}")
    m5_df = pd.DataFrame(m5_list)
    h1_df = pd.DataFrame(h1_list)

    setups = load_setups()
    print(f"\n{len(setups)} Beta setups, computing filters + outcomes...")

    enriched = []
    for s in setups:
        flt = filters_for(s, h1_df, m5_df)
        outcome, pips = resolve_trade(s, m1_list)
        enriched.append({**s, **flt, "outcome": outcome, "pips": pips})

    # Per-setup table
    print(f"\n{'time(UTC)':<18}{'dir':<5}{'entry':>9}{'h1':>9}"
          f"{'F1':>4}{'F2':>4}{'F3':>4}{'F4':>4}{'out':>6}{'pips':>7}")
    for r in enriched:
        ts = r["t"].strftime("%m-%d %H:%M")
        print(f"{ts:<18}{r['dir']:<5}{r['entry']:>9.2f}{r['h1b']:>9}"
              f"{int(r['f1']):>4}{int(r['f2']):>4}{int(r['f3']):>4}{int(r['f4']):>4}"
              f"{r['outcome']:>6}{r['pips']:>+7d}")

    # Mask sweep — for each (e1,e2,e3,e4) ∈ {0,1}^4, compute net
    print(f"\n--- Mask sweep (16 combinations, Bot.py geometry) ---")
    print(f"{'F1':>3}{'F2':>3}{'F3':>3}{'F4':>3}  {'taken':>6}{'TP2':>5}{'BE':>4}{'SL':>4}{'net':>8}")
    results = []
    for e1, e2, e3, e4 in product([0, 1], repeat=4):
        taken = []
        for r in enriched:
            blocked = (e1 and r["f1"]) or (e2 and r["f2"]) or (e3 and r["f3"]) or (e4 and r["f4"])
            if not blocked:
                taken.append(r)
        net = sum(r["pips"] for r in taken if r["outcome"] != "OPEN")
        tp2 = sum(1 for r in taken if r["outcome"] == "TP2")
        be  = sum(1 for r in taken if r["outcome"] == "BE")
        sl  = sum(1 for r in taken if r["outcome"] == "SL")
        results.append({"mask": (e1,e2,e3,e4), "taken": len(taken), "tp2": tp2, "be": be, "sl": sl, "net": net})

    for r in sorted(results, key=lambda x: -x["net"]):
        m = r["mask"]
        marker = ""
        if m == (0,1,0,0): marker = "  ← Beta default (FTFF)"
        if m == (1,1,1,1): marker = "  ← Bot.py-equivalent (TTTT)"
        print(f"{m[0]:>3}{m[1]:>3}{m[2]:>3}{m[3]:>3}  {r['taken']:>6}{r['tp2']:>5}{r['be']:>4}{r['sl']:>4}{r['net']:>+8d}{marker}")

    print("\nBot.py replay (its own setups, TTTT geometry) was +1,415 — see backtest.py")


if __name__ == "__main__":
    main()
