"""
RaphaelBeta2 backtest — replays Beta's detected setups from 4 May (Mon) onward
using Bot.py risk geometry (TP1=4.5, TP2=9.5, SL cap 20p, BE-shift after TP1).

Resolution: M5 OHLC from OANDA. Conservative tie-break inside a bar → SL before TP.
"""

import csv
import os
from datetime import datetime, timedelta, timezone
from pathlib import Path

from dotenv import load_dotenv
import oandapyV20
import oandapyV20.endpoints.instruments as instruments

PKG = Path(__file__).resolve().parent
load_dotenv(PKG / ".env")
OANDA_KEY = os.environ["OANDA_KEY"]
oanda = oandapyV20.API(access_token=OANDA_KEY)

# RaphaelBeta2 geometry (Bot.py rules)
TP1_DIST = 4.5
TP2_DIST = 9.5
MAX_SL   = 20.0

BACKTEST_FROM = datetime(2026, 5, 4, 0, 0, tzinfo=timezone.utc)
BACKTEST_TO   = datetime.now(timezone.utc) - timedelta(minutes=10)
INSTRUMENT    = "XAU_USD"

BETA_LOG = Path("/Users/user/Desktop/RaphaelBeta/signals_log.csv")
BOT_LOG  = Path("/Users/user/Desktop/Raphael/signals_log.csv")


def fetch_candles(from_dt: datetime, to_dt: datetime, granularity: str = "M1"):
    """Fetch candles between from_dt and to_dt (UTC), chunked by day."""
    out = []
    cursor = from_dt
    step = timedelta(hours=12 if granularity == "M1" else 24)
    while cursor < to_dt:
        chunk_to = min(cursor + step, to_dt)
        params = {
            "granularity": granularity,
            "from": cursor.isoformat().replace("+00:00", "Z"),
            "to":   chunk_to.isoformat().replace("+00:00", "Z"),
            "price": "M",
        }
        r = instruments.InstrumentsCandles(INSTRUMENT, params=params)
        oanda.request(r)
        cs = r.response["candles"]
        if not cs:
            cursor = chunk_to
            continue
        for c in cs:
            t = datetime.fromisoformat(c["time"].replace("Z", "+00:00"))
            out.append({
                "t": t,
                "o": float(c["mid"]["o"]),
                "h": float(c["mid"]["h"]),
                "l": float(c["mid"]["l"]),
                "c": float(c["mid"]["c"]),
            })
        last_t = out[-1]["t"]
        if last_t <= cursor:
            break
        cursor = last_t + timedelta(minutes=1 if granularity == "M1" else 5)
    return out


LOCAL_UTC_OFFSET = timedelta(hours=8)  # CSV timestamps are UTC+8 (datetime.now())


def load_opens(path, start: datetime):
    """Read a signals_log.csv; return OPEN signals on/after start (UTC)."""
    rows = []
    with open(path) as f:
        for r in csv.DictReader(f):
            if r["status"] != "OPEN":
                continue
            local_t = datetime.fromisoformat(r["time"])
            t = (local_t - LOCAL_UTC_OFFSET).replace(tzinfo=timezone.utc)
            if t < start:
                continue
            rows.append({
                "t": t,
                "dir": r["type"],
                "entry": float(r["entry"]),
                "beta_sl_dist": float(r["sl_distance"]),
            })
    return rows


def resolve_trade(setup, candles, tp1_dist, tp2_dist, max_sl, runner_mode,
                  runner_lock=1.5):
    """Walk candles forward; return (status, exit_price, pips).
       runner_mode: BE | NONE | LOCK (LOCK uses runner_lock USD)."""
    direction = setup["dir"]
    entry     = setup["entry"]

    sl_dist = min(setup["beta_sl_dist"], max_sl)
    if direction == "BUY":
        sl  = entry - sl_dist
        tp1 = entry + tp1_dist
        tp2 = entry + tp2_dist
        lock_level = entry + runner_lock
    else:
        sl  = entry + sl_dist
        tp1 = entry - tp1_dist
        tp2 = entry - tp2_dist
        lock_level = entry - runner_lock

    tp1_hit = False
    sl_now  = sl
    pips    = 0

    for c in candles:
        # Skip candles strictly before entry, and the candle containing the
        # entry timestamp (we don't know what part of that bar happened pre-entry)
        if c["t"] <= setup["t"]:
            continue
        hi, lo = c["h"], c["l"]

        if direction == "BUY":
            sl_touched  = lo <= sl_now
            tp1_touched = hi >= tp1
            tp2_touched = hi >= tp2
        else:
            sl_touched  = hi >= sl_now
            tp1_touched = lo <= tp1
            tp2_touched = lo <= tp2

        if not tp1_hit:
            if sl_touched:
                return "SL_HIT", sl, -int(round(abs(entry - sl) * 10))
            if tp1_touched:
                tp1_hit = True
                pips = int(round(tp1_dist * 10))
                if runner_mode == "BE":
                    sl_now = entry
                elif runner_mode == "LOCK":
                    sl_now = lock_level
                # NONE: keep structure sl
                if tp2_touched:
                    return "TP2_HIT", tp2, int(round(tp2_dist * 10))
                continue

        # post-TP1
        if direction == "BUY":
            stop_touched = lo <= sl_now
        else:
            stop_touched = hi >= sl_now

        if stop_touched and tp2_touched:
            # pessimistic tie-break: stop first
            if runner_mode == "BE":
                return "BE_HIT", sl_now, 0
            if runner_mode == "LOCK":
                return "LOCK_HIT", sl_now, int(round(runner_lock * 10))
            return "RUNNER_SL_HIT", sl_now, -int(round(abs(entry - sl_now) * 10))
        if stop_touched:
            if runner_mode == "BE":
                return "BE_HIT", sl_now, 0
            if runner_mode == "LOCK":
                return "LOCK_HIT", sl_now, int(round(runner_lock * 10))
            return "RUNNER_SL_HIT", sl_now, -int(round(abs(entry - sl_now) * 10))
        if tp2_touched:
            return "TP2_HIT", tp2, int(round(tp2_dist * 10))

    # Out of candles — open trade, count nothing
    return "OPEN_END", None, pips


def summarise_log(path, label, start):
    """Summarise an existing signals_log.csv for comparison."""
    closes = []
    with open(path) as f:
        for r in csv.DictReader(f):
            local_t = datetime.fromisoformat(r["time"])
            t = (local_t - LOCAL_UTC_OFFSET).replace(tzinfo=timezone.utc)
            if t < start: continue
            if r["status"] == "OPEN": continue
            closes.append(r)
    pips = sum(int(r["pips"] or 0) for r in closes)
    wins = sum(1 for r in closes if r["status"] in ("TP1_HIT","TP2_HIT"))
    losses = sum(1 for r in closes if r["status"] in ("SL_HIT","RUNNER_SL_HIT"))
    bes = sum(1 for r in closes if r["status"] == "BE_HIT")
    return {
        "label": label,
        "closures": len(closes),
        "wins": wins,
        "losses": losses,
        "be": bes,
        "pips": pips,
    }


def replay(setups, candles, tp1_dist, tp2_dist, max_sl, runner_mode, label):
    by_status = {}
    net = 0
    rows = []
    for s in setups:
        status, exit_p, pips = resolve_trade(
            s, candles, tp1_dist, tp2_dist, max_sl, runner_mode
        )
        by_status[status] = by_status.get(status, 0) + 1
        net += pips
        rows.append({**s, "status": status, "pips": pips})
    return {"label": label, "rows": rows, "by_status": by_status, "net": net,
            "tp1": tp1_dist, "tp2": tp2_dist, "sl": max_sl, "runner": runner_mode}


def print_summary(res):
    bs = res["by_status"]
    wins   = bs.get("TP1_HIT", 0) + bs.get("TP2_HIT", 0)
    losses = bs.get("SL_HIT", 0) + bs.get("RUNNER_SL_HIT", 0)
    be     = bs.get("BE_HIT", 0)
    lock   = bs.get("LOCK_HIT", 0)
    open_  = bs.get("OPEN_END", 0)
    closed = wins + losses + be + lock
    print(f"  {res['label']:<24} TP2={bs.get('TP2_HIT',0)} "
          f"BE={be} LOCK={lock} SL={bs.get('SL_HIT',0)} RunnerSL={bs.get('RUNNER_SL_HIT',0)} "
          f"open={open_}  closed={closed}  net={res['net']:+d}")


def main():
    print(f"Fetching M1 candles {BACKTEST_FROM} → {BACKTEST_TO} ...")
    candles = fetch_candles(BACKTEST_FROM, BACKTEST_TO, "M1")
    print(f"  got {len(candles)} M1 candles")

    bot_setups  = load_opens(BOT_LOG,  BACKTEST_FROM)
    beta_setups = load_opens(BETA_LOG, BACKTEST_FROM)
    print(f"\nBot.py setups:  {len(bot_setups)}")
    print(f"Beta setups:    {len(beta_setups)}")
    print(f"RaphaelBeta2 inherits Beta's detection mask (FTFF), so uses Beta's setups.\n")

    bot_res  = replay(bot_setups,  candles, 4.5, 9.5, 20.0, "BE",   "Bot.py")
    beta_res = replay(beta_setups, candles, 6.5, 22.0, 30.0, "NONE", "Beta")
    rb2_res  = replay(beta_setups, candles, 4.5, 9.5, 20.0, "BE",   "RaphaelBeta2 (BE)")
    rb2_lock = replay(beta_setups, candles, 4.5, 9.5, 20.0, "LOCK", "RaphaelBeta2 (LOCK 1.5)")

    print(f"--- Trade-by-trade (RaphaelBeta2) ---")
    print(f"{'time(UTC)':<22}{'dir':<5}{'entry':>10}{'status':>15}{'pips':>8}")
    for r in rb2_res["rows"]:
        ts = r["t"].strftime("%Y-%m-%d %H:%M")
        print(f"{ts:<22}{r['dir']:<5}{r['entry']:>10.2f}{r['status']:>15}{r['pips']:>+8d}")

    print(f"\n--- Head-to-head (M1 replay, 4 May → now) ---")
    for res in (bot_res, beta_res, rb2_res, rb2_lock):
        print_summary(res)


if __name__ == "__main__":
    main()
