"""Sweep TP1/TP2/SL geometry on Beta's 23 setups, all with BE runner mode."""
import csv
from datetime import datetime, timedelta, timezone
from pathlib import Path
import os
from dotenv import load_dotenv
import oandapyV20
import oandapyV20.endpoints.instruments as instruments

PKG = Path(__file__).resolve().parent
load_dotenv(PKG / ".env")
oanda = oandapyV20.API(access_token=os.environ["OANDA_KEY"])

LOCAL_OFFSET = timedelta(hours=8)
START = datetime(2026, 5, 4, 0, 0, tzinfo=timezone.utc)
END   = datetime.now(timezone.utc) - timedelta(minutes=5)


def fetch_m1(from_dt, to_dt):
    out, cursor = [], from_dt
    while cursor < to_dt:
        ct = min(cursor + timedelta(hours=12), to_dt)
        params = {"granularity": "M1", "price": "M",
                  "from": cursor.isoformat().replace("+00:00", "Z"),
                  "to":   ct.isoformat().replace("+00:00", "Z")}
        r = instruments.InstrumentsCandles("XAU_USD", params=params); oanda.request(r)
        cs = r.response["candles"]
        if not cs: cursor = ct; continue
        for c in cs:
            out.append({"t": datetime.fromisoformat(c["time"].replace("Z", "+00:00")),
                        "h": float(c["mid"]["h"]), "l": float(c["mid"]["l"])})
        if out[-1]["t"] <= cursor: break
        cursor = out[-1]["t"] + timedelta(minutes=1)
    return out


def setups():
    rows = []
    with open("/Users/user/Desktop/RaphaelBeta/signals_log.csv") as f:
        for r in csv.DictReader(f):
            if r["status"] != "OPEN": continue
            t = (datetime.fromisoformat(r["time"]) - LOCAL_OFFSET).replace(tzinfo=timezone.utc)
            if t < START: continue
            rows.append({"t": t, "dir": r["type"], "entry": float(r["entry"]),
                         "beta_sl_dist": float(r["sl_distance"])})
    return rows


def resolve(setup, m1, tp1d, tp2d, slmax):
    d, e = setup["dir"], setup["entry"]
    sld = min(setup["beta_sl_dist"], slmax)
    if d == "BUY":  sl, tp1, tp2 = e - sld, e + tp1d, e + tp2d
    else:           sl, tp1, tp2 = e + sld, e - tp1d, e - tp2d
    tp1_hit, sln = False, sl
    for c in m1:
        if c["t"] <= setup["t"]: continue
        if d == "BUY":
            slt, t1t, t2t = c["l"] <= sln, c["h"] >= tp1, c["h"] >= tp2
        else:
            slt, t1t, t2t = c["h"] >= sln, c["l"] <= tp1, c["l"] <= tp2
        if not tp1_hit:
            if slt: return -int(round(abs(e - sl) * 10))
            if t1t:
                tp1_hit = True; sln = e
                if t2t: return int(round(tp2d * 10))
                continue
        if d == "BUY": be_t = c["l"] <= sln
        else:          be_t = c["h"] >= sln
        if be_t and not t2t: return 0
        if t2t: return int(round(tp2d * 10))
    return 0


def main():
    print("Fetching M1 candles...")
    m1 = fetch_m1(START, END)
    sps = setups()
    print(f"  {len(m1)} candles, {len(sps)} setups\n")

    # Sweep
    candidates = []
    for tp1 in [3.5, 4.0, 4.5, 5.0, 5.5]:
        for tp2 in [7.5, 8.5, 9.5, 10.5, 11.5]:
            if tp2 <= tp1 + 2: continue
            for slm in [12.0, 15.0, 18.0, 20.0, 25.0]:
                net = sum(resolve(s, m1, tp1, tp2, slm) for s in sps)
                candidates.append({"tp1": tp1, "tp2": tp2, "sl": slm, "net": net})

    candidates.sort(key=lambda x: -x["net"])
    print(f"{'TP1':>5}{'TP2':>6}{'MAX_SL':>8}{'net':>8}")
    seen = set()
    for c in candidates:
        key = (c["tp1"], c["tp2"])
        if key in seen: continue
        seen.add(key)
        marker = "  ← Bot.py" if (c["tp1"], c["tp2"], c["sl"]) == (4.5, 9.5, 20.0) else ""
        print(f"{c['tp1']:>5.1f}{c['tp2']:>6.1f}{c['sl']:>8.1f}{c['net']:>+8d}{marker}")
    print(f"\n... {len(candidates)} total combos, Bot.py geometry shown above.")


if __name__ == "__main__":
    main()
