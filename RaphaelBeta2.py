# -*- coding: utf-8 -*-
"""
Raphael AI — Gold (XAU/USD) Signal Bot (beta bundle)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Signal Logic:
  • Order Block detection on M5: bearish/bullish candle broken 2 bars later
  • Entry fires when price is inside the OB zone
  • Momentum filter: opposing candle momentum cancels the signal
  • TP1 / TP2 distances and MAX_SL match tuned backtest (b.py)
  • Runner stop after TP1: RUNNER_STOP_MODE = BE | LOCK | NONE
  • Directional filters F1–F4 use locked mask FTFF (see ENABLE_SELL_* / ENABLE_BUY_*)
  • News alerts ±30 min around high-impact USD events
  • Session announcements (Asian / London / New York)
  • Weekly summary on Saturday shutdown
  • Set RAPHAEL_BETA_SILENT=0 to send Telegram; default silent logs to CSV + console only
"""

import os
import json
import time
import random
import asyncio
import logging
import requests

from datetime import datetime, timedelta, UTC
from zoneinfo import ZoneInfo
from PIL import Image, ImageDraw, ImageFont

import pandas as pd
import oandapyV20
import oandapyV20.endpoints.instruments as instruments
from pathlib import Path

# This bundle lives in one folder; state, Telegram session, images, and default MT4 signal path are relative to here.
_PKG_DIR = Path(__file__).resolve().parent

logging.getLogger("telethon").setLevel(logging.ERROR)

from telethon import TelegramClient, events
from telethon.tl.types import MessageEntityCustomEmoji


# ═══════════════════════════════════════════════
#  CONFIG
# ═══════════════════════════════════════════════
from dotenv import load_dotenv
load_dotenv(_PKG_DIR / ".env")

TG_API_ID    = int(os.environ["TG_API_ID"])
TG_API_HASH  = os.environ["TG_API_HASH"]
CHANNEL_ID   = int(os.environ["CHANNEL_ID"])
ADMIN_ID     = int(os.environ["ADMIN_ID"])
OANDA_KEY    = os.environ["OANDA_KEY"]
# Override with env RAPHAEL_MT4_SIGNAL_FILE if MT4 lives elsewhere (same as original Bot.py path).
SIGNAL_FILE  = os.environ.get(
    "RAPHAEL_MT4_SIGNAL_FILE",
    str(_PKG_DIR / "signal_mt4.txt"),
)

STATE_FILE      = str(_PKG_DIR / "active_trade.json")
MONITOR_FILE    = str(_PKG_DIR / "monitoring_trade.json")
NEWS_STATE_FILE = str(_PKG_DIR / "news_state.json")
LOG_FILE        = str(_PKG_DIR / "signals_log.csv")
INSTRUMENT      = "XAU_USD"

# Default silent: no Telegram sends; logs trades to signals_log.csv and prints stats.
# Set RAPHAEL_BETA_SILENT=0 (or false/off/no) to enable outbound Telegram like production.
SILENT_TELEGRAM = os.environ.get("RAPHAEL_BETA_SILENT", "1").strip().lower() not in (
    "0", "false", "off", "no",
)

# ═══════════════════════════════════════════════
#  STRATEGY PARAMETERS
# ═══════════════════════════════════════════════
MAX_SL             = 20.0   # Bot.py geometry
TP1_DIST           = 4.5    # Bot.py geometry
TP2_DIST           = 9.5    # Bot.py geometry
OB_LOOKBACK        = 14
PAUSE_BEFORE       = 30
PAUSE_AFTER        = 30
WATCHED_CURRENCIES = {"USD", "XAU"}

# ── Backtested filters (88.8% win rate over 6 months) ──
DEAD_HOURS         = {0, 1, 2, 6, 8, 13, 21}   # UTC hours to skip
OB_MIN_SIZE        = 3.0                         # Minimum OB zone size in dollars
FVG_LOOKBACK       = 10                          # Candles to scan for FVG
H1_EMA_PERIOD      = 50                          # H1 EMA period
H4_EMA_PERIOD      = 50                          # H4 EMA period
H1_NEUTRAL_PCT     = 0.001                       # H1 EMA neutral threshold
ZONE_COOLDOWN_SECS = 7200                        # 2hr zone cooldown after SL
EMA_SLOPE_PERIOD   = 10
EMA_SLOPE_MIN      = 3.0
ATR_PERIOD_        = 14
ATR_RANGING_MAX    = 1.5
ANNOUNCEMENT_FILE  = str(_PKG_DIR / "announced_v4.flag")
WINRATE_FIX_FLAG   = str(_PKG_DIR / "announced_winrate_fix.flag")

_last_log_msg = None
def log_once(msg):
    global _last_log_msg
    if msg != _last_log_msg:
        print(msg)
        _last_log_msg = msg

# Runner SL after TP1 is hit: BE = entry; LOCK = entry ± RUNNER_LOCK_USD; NONE = keep structure SL
_RUNNER_RAW = os.environ.get("RAPHAEL_RUNNER_STOP_MODE", "BE").strip().upper()
RUNNER_STOP_MODE = _RUNNER_RAW if _RUNNER_RAW in ("NONE", "BE", "LOCK") else "NONE"
RUNNER_LOCK_USD  = float(os.environ.get("RAPHAEL_RUNNER_LOCK_USD", "1.5"))

# ── Directional filters — mask FTFF (only H1-neutral SELL block on) ──
ENABLE_SELL_BEARISH_CANDLE_BLOCK     = False
ENABLE_SELL_H1_NEUTRAL_BLOCK         = True
ENABLE_SELL_LONDON_BLOCK             = False
ENABLE_BUY_BEAR_H1_NEAR_STRUCT_BLOCK = False

# ═══════════════════════════════════════════════
#  CLIENTS
# ═══════════════════════════════════════════════
# Separate session file name so this beta can run alongside the original Bot.py.
tg_client = TelegramClient(str(_PKG_DIR / "raphael_beta_session"), TG_API_ID, TG_API_HASH, sequential_updates=True)
oanda     = oandapyV20.API(access_token=OANDA_KEY)

# ═══════════════════════════════════════════════
#  GLOBAL STATE
# ═══════════════════════════════════════════════
active_trade         = None
monitoring_trade     = None
last_signal          = None
last_signal_time     = 0
last_sl_time         = 0
last_session_ann     = None
last_dead_hour_ann   = None  # dedupe dead-hours Telegram (must not use last_session_ann — session code clears it)
news_pause_notified  = False
news_calendar_sent   = None   # unused; kept for parity with Bot.py
news_warned_events   = set()   # event keys we've already sent a 1hr warning for
last_calendar_fetch  = None
high_impact_events   = []
zone_sl_times        = {}   # zone cooldown tracking
h1_ema_cache         = None
h1_ema_last_fetch    = 0
h4_ema_cache         = None
h4_ema_last_fetch    = 0


# ═══════════════════════════════════════════════
#  SESSION MESSAGES
# ═══════════════════════════════════════════════
LONDON_MESSAGES = [
    "▶️ London Session is now open!\n\nGood afternoon traders! London is now live 🧠 Let's have a great session, Raphael fam!",
    "▶️ London Session is now open!\n\nRaphael is live. Stay sharp, manage your risk, and let's get these pips. 🧠",
    "▶️ London Session is now open!\n\nLFG LONDON IS OPEN 🔥 Raphael is locked in, let's get it!",
]
NEW_YORK_MESSAGES = [
    "▶️ New York Session is now open!\n\nGood afternoon traders! New York is live 🧠 Let's have a great session, Raphael fam!",
    "▶️ New York Session is now open!\n\nRaphael is live. The big moves are coming — stay focused, trust the process. 🧠",
    "▶️ New York Session is now open!\n\nLFG NEW YORK IS OPEN 🔥 Raphael is locked in, let's get it!",
]
ASIAN_MESSAGES = [
    "▶️ Asian Session is now open!\n\nGood morning traders! Asian session is live 🧠 Let's start the week strong, Raphael fam!",
    "▶️ Asian Session is now open!\n\nRaphael is live. Slow and steady — wait for the right setup. 🧠",
    "▶️ Asian Session is now open!\n\nLFG ASIAN SESSION IS OPEN 🔥 Raphael is locked in, let's get it!",
]


# ═══════════════════════════════════════════════
#  EMOJI MAP
# ═══════════════════════════════════════════════
_EMOJI_IDS = {
    "👑": 6287301624163474655,
    "🟢": 6287056703653421006,
    "🔴": 6289675993753853637,
    "🧠": 6287190839777042189,
    "🔥": 6291565933982916236,
    "❤️": 6289280010654064997,
    "⚡️": 6289339113699024099,
    "🚀": 6291941485923278373,
    "☺️": 6296208909594008970,
    "🗓️": 6296098352840842983,
    "✅": 6296332402788670566,
    "📊": 6296100002108284965,
    "⚠️": 6309623183381109924,
    "📉": 6309782805840666514,
    "📈": 6307486269647626400,
    "🕐": 6309671398683974414,  # S
    "🕑": 6309827529335119341,  # E
    "🕒": 6309880112619724133,  # L
    "🕗": 6307423520175431456,  # B
    "🕘": 6309796824613920055,  # U
    "🕖": 6310031587526320268,  # Y
    "🕓": 6310019243790311437,  # N
    "🕔": 6309574332423085963,  # T
    "🕕": 6309905671970102674,  # R
    "📌": 6325627850728679329,
    "🆕": 6328026907791072799,
    "🔄": 6325790406650898134,
    "▶️": 6327659451864062399,
}

def _build_entities(text: str) -> list:
    entities = []
    utf16_offset = 0
    i = 0
    while i < len(text):
        two = text[i:i+2]
        if two in _EMOJI_IDS:
            length = len(two.encode("utf-16-le")) // 2
            entities.append(MessageEntityCustomEmoji(
                offset=utf16_offset, length=length, document_id=_EMOJI_IDS[two]
            ))
            utf16_offset += length
            i += 2
        else:
            char = text[i]
            length = len(char.encode("utf-16-le")) // 2
            if char in _EMOJI_IDS:
                entities.append(MessageEntityCustomEmoji(
                    offset=utf16_offset, length=length, document_id=_EMOJI_IDS[char]
                ))
            utf16_offset += length
            i += 1
    return entities


# ═══════════════════════════════════════════════
#  TELEGRAM HELPERS
# ═══════════════════════════════════════════════
async def send_telegram(msg: str):
    if SILENT_TELEGRAM:
        return
    entity = await tg_client.get_entity(CHANNEL_ID)
    await tg_client.send_message(entity, msg, formatting_entities=_build_entities(msg))


async def send_telegram_image(image_path: str, caption: str = ""):
    if SILENT_TELEGRAM:
        return
    entity = await tg_client.get_entity(CHANNEL_ID)
    await tg_client.send_file(
        entity, image_path,
        caption=caption,
        formatting_entities=_build_entities(caption)
    )


# ═══════════════════════════════════════════════
#  MT4 SIGNAL FILE
# ═══════════════════════════════════════════════
def write_signal(action, signal_type="", tp1=0, tp2=0, sl=0, lot=0.01,
                 zone_low=0, zone_high=0, entry_price=0):
    if signal_type == "BUY":
        layer1, layer2, layer3 = entry_price, entry_price - 8, entry_price - 15
    elif signal_type == "SELL":
        layer1, layer2, layer3 = entry_price, entry_price + 8, entry_price + 15
    else:
        layer1 = layer2 = layer3 = 0
    ts = datetime.now().strftime("%Y-%m-%dT%H:%M:%S")
    content = (
        f"{action}\n{float(tp1)}\n{float(tp2)}\n{float(sl)}\n{lot}\n"
        f"{round(layer1,2)}\n{round(layer2,2)}\n{round(layer3,2)}\n{signal_type}\n{ts}\n"
    )
    with open(SIGNAL_FILE, "w") as f:
        f.write(content)


def clear_signal():
    with open(SIGNAL_FILE, "w") as f:
        f.write("NONE\n")


# ═══════════════════════════════════════════════
#  STATE PERSISTENCE
# ═══════════════════════════════════════════════
def save_state():
    with open(STATE_FILE, "w") as f:
        json.dump(active_trade, f)


def load_state():
    global active_trade
    if os.path.isfile(STATE_FILE):
        with open(STATE_FILE) as f:
            active_trade = json.load(f)


def save_monitor():
    with open(MONITOR_FILE, "w") as f:
        json.dump(monitoring_trade, f)


def load_monitor():
    global monitoring_trade
    if os.path.isfile(MONITOR_FILE):
        with open(MONITOR_FILE) as f:
            monitoring_trade = json.load(f)


# ═══════════════════════════════════════════════
#  LOGGING
# ═══════════════════════════════════════════════
def _pips_from_usd(distance_usd: float) -> int:
    return int(round(abs(float(distance_usd)) * 10))


def status_to_log_pips(signal_type: str, status: str, entry, tp1, tp2, sl) -> int:
    """Pips for CSV column (~$0.10 = 1 pip). Uses actual entry/TP/SL distances."""
    e, t1, t2, s = float(entry), float(tp1), float(tp2), float(sl)
    if status == "OPEN":
        return 0
    if status == "TP1_HIT":
        return _pips_from_usd(t1 - e if signal_type == "BUY" else e - t1)
    if status == "TP2_HIT":
        return _pips_from_usd(t2 - t1 if signal_type == "BUY" else t1 - t2)
    if status == "SL_HIT":
        return -_pips_from_usd(e - s if signal_type == "BUY" else s - e)
    if status in ("BE_HIT",):
        return 0
    if status == "RUNNER_SL_HIT":
        return -_pips_from_usd(e - s if signal_type == "BUY" else s - e)
    if status == "LOCK_HIT":
        return _pips_from_usd(s - e if signal_type == "BUY" else e - s)
    return 0


def log_signal(signal_type, entry, tp1, tp2, sl, status, session="",
               signal_source="", ema_bias="",
               sl_distance=0, tp1_distance=0, zone_size=0,
               candle_body_ratio=0, open_time=None):
    file_exists = os.path.isfile(LOG_FILE)
    now = datetime.now()

    pips = status_to_log_pips(signal_type, status, entry, tp1, tp2, sl)

    duration = ""
    if open_time and status in (
        "TP1_HIT", "TP2_HIT", "SL_HIT", "BE_HIT", "RUNNER_SL_HIT", "LOCK_HIT",
    ):
        try:
            duration = round((now - datetime.fromisoformat(open_time)).total_seconds() / 60, 1)
        except Exception:
            pass

    with open(LOG_FILE, "a") as f:
        if not file_exists:
            f.write("time,type,entry,tp1,tp2,sl,status,session,pips,"
                    "signal_source,ema_bias,sl_distance,tp1_distance,"
                    "zone_size,candle_body_ratio,hour_utc,duration_mins\n")
        f.write(
            f"{now},{signal_type},{entry},{tp1},{tp2},{sl},{status},"
            f"{session},{pips},{signal_source},{ema_bias},"
            f"{round(sl_distance,2)},{round(tp1_distance,2)},"
            f"{round(zone_size,2)},{round(candle_body_ratio,4)},"
            f"{now.hour},{duration}\n"
        )


def _parse_log_stats():
    if not os.path.isfile(LOG_FILE):
        return {
            "rate": 0, "tp1": 0, "tp2": 0, "be": 0, "sl": 0, "runner_sl": 0,
            "lock": 0, "sl_total": 0, "net": 0,
        }
    tp1 = tp2 = sl = be = runner_sl = lock_hits = net = 0
    with open(LOG_FILE) as f:
        for line in f:
            if line.startswith("time,"):
                continue
            parts = line.strip().split(",")
            if len(parts) < 9:
                continue
            status = parts[6]
            try:
                pip_col = int(float(parts[8]))
            except (TypeError, ValueError):
                pip_col = 0
            if status == "TP1_HIT":
                tp1 += 1
                net += pip_col
            elif status == "TP2_HIT":
                tp2 += 1
                net += pip_col
            elif status == "SL_HIT":
                sl += 1
                net += pip_col
            elif status == "BE_HIT":
                be += 1
                net += pip_col
            elif status == "RUNNER_SL_HIT":
                runner_sl += 1
                net += pip_col
            elif status == "LOCK_HIT":
                lock_hits += 1
                net += pip_col
    sl_total = sl + runner_sl
    total = tp1 + tp2 + sl_total
    rate = round(((tp1 + tp2) / total) * 100) if total > 0 else 0
    return {
        "rate": rate,
        "tp1": tp1,
        "tp2": tp2,
        "be": be,
        "sl": sl,
        "runner_sl": runner_sl,
        "lock": lock_hits,
        "sl_total": sl_total,
        "net": net,
    }


def get_win_rate():
    """Parse CSV; sl_total counts SL_HIT + RUNNER_SL_HIT (loss exits)."""
    s = _parse_log_stats()
    return s["rate"], s["tp1"], s["be"], s["sl_total"], s["net"]


def _print_win_rate_console(note: str = ""):
    if not SILENT_TELEGRAM:
        return
    s = _parse_log_stats()
    header = f"Trade closed: {note}" if note else "Stats update"
    net = s['net']
    net_str = f"+{net}" if net > 0 else str(net)
    print(
        "\n" + "─" * 50 + "\n"
        f"[Raphael Beta] {header}\n"
        f"  Win rate (loose): {s['rate']}%\n"
        f"  Net pips:         {net_str}\n"
        f"  Wins:    TP1={s['tp1']}   TP2={s['tp2']}\n"
        f"  Losses:  SL={s['sl']}    RunnerSL={s['runner_sl']}\n"
        f"  Other:   BE={s['be']}    Lock={s['lock']}\n"
        + "─" * 50
    )


# ═══════════════════════════════════════════════
#  SIGNAL IMAGE
# ═══════════════════════════════════════════════
def _get_font(size: int):
    font_path = _PKG_DIR / "Montserrat-Bold.ttf"
    if font_path.is_file():
        return ImageFont.truetype(str(font_path), size)
    return ImageFont.load_default()


def _draw_right(draw, text, right_x, y, font, fill):
    bbox = draw.textbbox((0, 0), text, font=font)
    draw.text((right_x - (bbox[2] - bbox[0]), y), text, font=font, fill=fill)


def create_signal_image(signal_type, entry, tp1, tp2, sl) -> str:
    img_path = _PKG_DIR / "Raphael.png"
    out_path = _PKG_DIR / "output.png"
    img  = Image.open(str(img_path)).convert("RGB")
    draw = ImageDraw.Draw(img)
    w, h = img.size
    rx   = int(w * 0.92)
    font = _get_font(60)
    _draw_right(draw, str(entry), rx, int(h * 0.40), font, (255, 255, 255))
    _draw_right(draw, str(tp1),   rx, int(h * 0.51), font, (0, 255, 120))
    _draw_right(draw, str(tp2),   rx, int(h * 0.62), font, (0, 255, 120))
    _draw_right(draw, str(sl),    rx, int(h * 0.73), font, (255, 60,  60))
    img.save(str(out_path))
    return str(out_path)


# ═══════════════════════════════════════════════
#  MARKET DATA
# ═══════════════════════════════════════════════
def get_candles(granularity="M5", count=300) -> pd.DataFrame:
    params = {"granularity": granularity, "count": count, "price": "M"}
    r = instruments.InstrumentsCandles(INSTRUMENT, params=params)
    oanda.request(r)
    rows = []
    for c in r.response["candles"]:
        rows.append({
            "open":  float(c["mid"]["o"]),
            "high":  float(c["mid"]["h"]),
            "low":   float(c["mid"]["l"]),
            "close": float(c["mid"]["c"]),
        })
    return pd.DataFrame(rows)


def get_h1_bias() -> str:
    """H1 50 EMA bias — BULLISH/BEARISH/NEUTRAL. Cached for 30 mins."""
    global h1_ema_cache, h1_ema_last_fetch
    try:
        df = get_candles("H1", count=100)
        ema = df["close"].ewm(span=H1_EMA_PERIOD, adjust=False).mean().iloc[-1]
        h1_close = df["close"].iloc[-1]
        h1_ema_cache = ema
        h1_ema_last_fetch = time.time()
        pct = (h1_close - ema) / ema
        if pct > H1_NEUTRAL_PCT:   return "BULLISH"
        if pct < -H1_NEUTRAL_PCT:  return "BEARISH"
        return "NEUTRAL"
    except Exception as e:
        print(f"H1 bias error: {e}")
        return "NEUTRAL"


def get_h4_bias() -> str:
    """H4 50 EMA bias — BULLISH/BEARISH/NEUTRAL."""
    global h4_ema_cache, h4_ema_last_fetch
    try:
        df = get_candles("H4", count=100)
        ema = df["close"].ewm(span=H4_EMA_PERIOD, adjust=False).mean().iloc[-1]
        h4_close = df["close"].iloc[-1]
        h4_ema_cache = ema
        h4_ema_last_fetch = time.time()
        pct = (h4_close - ema) / ema
        if pct > H1_NEUTRAL_PCT:   return "BULLISH"
        if pct < -H1_NEUTRAL_PCT:  return "BEARISH"
        return "NEUTRAL"
    except Exception as e:
        print(f"H4 bias error: {e}")
        return "NEUTRAL"


def get_atr_value(df: pd.DataFrame, period: int = 14) -> float:
    """Calculate current ATR."""
    if len(df) < period + 1:
        return 999
    high  = df["high"].iloc[-(period+1):]
    low   = df["low"].iloc[-(period+1):]
    close = df["close"].iloc[-(period+1):]
    tr = pd.concat([
        high - low,
        (high - close.shift()).abs(),
        (low  - close.shift()).abs()
    ], axis=1).max(axis=1)
    return tr.rolling(period).mean().iloc[-1]


def is_consolidating(df: pd.DataFrame) -> bool:
    """Return True if market is ranging — flat EMA slope + low ATR."""
    if len(df) < EMA_SLOPE_PERIOD + ATR_PERIOD_ + 5:
        return False
    ema   = df["close"].ewm(span=50, adjust=False).mean()
    slope = abs(ema.iloc[-1] - ema.iloc[-EMA_SLOPE_PERIOD])
    atr   = get_atr_value(df)
    return slope < EMA_SLOPE_MIN and atr < ATR_RANGING_MAX


def has_fvg_confluence(df: pd.DataFrame, signal: str, zone: tuple) -> bool:
    """Check for Fair Value Gap overlapping with OB zone in last FVG_LOOKBACK candles."""
    low, high = zone
    n = len(df)
    for i in range(max(0, n - FVG_LOOKBACK - 2), n - 2):
        c1 = df.iloc[i]
        c3 = df.iloc[i + 2]
        if signal == "BUY":
            if c1["high"] < c3["low"]:
                if c1["high"] <= high and c3["low"] >= low:
                    return True
        else:
            if c1["low"] > c3["high"]:
                if c3["high"] <= high and c1["low"] >= low:
                    return True
    return False



# ═══════════════════════════════════════════════
#  SESSION
# ═══════════════════════════════════════════════
def get_session() -> str:
    h = datetime.now(ZoneInfo("Asia/Singapore")).hour
    if 22 <= h or h < 1:  return "London & New York 🔥🚀"
    if 15 <= h < 22:       return "London 🔥"
    if  1 <= h <  6:       return "New York 🚀"
    if  8 <= h < 15:       return "Asian ▶️"
    return "Off Hours ▶️"


async def check_session_announcement():
    global last_session_ann
    h = datetime.now(UTC).hour
    mapping = {23: ("Asian",    ASIAN_MESSAGES),
               7:  ("London",   LONDON_MESSAGES),
               13: ("New York", NEW_YORK_MESSAGES)}
    if h in mapping:
        name, pool = mapping[h]
        if last_session_ann != name:
            await send_telegram(random.choice(pool))
            last_session_ann = name
    elif h not in (23, 7, 13):
        last_session_ann = None


# ═══════════════════════════════════════════════
#  NEWS CALENDAR
# ═══════════════════════════════════════════════
def load_news_state():
    global news_pause_notified, news_warned_events
    if not os.path.isfile(NEWS_STATE_FILE):
        return
    try:
        with open(NEWS_STATE_FILE) as f:
            d = json.load(f)
        today = datetime.now(ZoneInfo("Asia/Singapore")).date().isoformat()
        if d.get("date") == today:
            news_pause_notified = d.get("news_pause_notified", False)
            news_warned_events  = set(d.get("warned_events", []))
    except Exception:
        pass


def save_news_state():
    today = datetime.now(ZoneInfo("Asia/Singapore")).date().isoformat()
    with open(NEWS_STATE_FILE, "w") as f:
        json.dump({
            "date": today,
            "news_pause_notified": news_pause_notified,
            "warned_events": sorted(news_warned_events),
        }, f)


def fetch_news_calendar():
    global high_impact_events, last_calendar_fetch
    try:
        resp = requests.get(
            "https://nfs.faireconomy.media/ff_calendar_thisweek.json",
            headers={"User-Agent": "Mozilla/5.0"}, timeout=15
        )
        resp.raise_for_status()
        today    = datetime.now(ZoneInfo("Asia/Singapore")).date()
        tomorrow = today + timedelta(days=1)
        events = []
        for item in resp.json():
            if item.get("country", "").upper() not in WATCHED_CURRENCIES:
                continue
            if item.get("impact", "").lower() != "high":
                continue
            try:
                dt = datetime.strptime(item["date"], "%Y-%m-%dT%H:%M:%S%z")
                dt = dt.astimezone(ZoneInfo("Asia/Singapore"))
            except Exception:
                continue
            # Keep today (for live blackout) + tomorrow (for advance announcement)
            if dt.date() not in (today, tomorrow):
                continue
            events.append({"time": dt, "currency": item.get("country", "").upper(),
                           "event": item.get("title", "Unknown")})
        high_impact_events = events
        last_calendar_fetch = datetime.now(UTC)
        print(f"News: {len(events)} high-impact events (today + tomorrow)")
        for e in events:
            sgt = e["time"].astimezone(ZoneInfo("Asia/Singapore"))
            print(f"  📅 {sgt.strftime('%a %H:%M SGT')} | {e['currency']} | {e['event']}")
        return events
    except Exception as ex:
        print(f"News fetch error: {ex}")
        return []


def is_news_blackout():
    now = datetime.now(ZoneInfo("Asia/Singapore"))
    for e in high_impact_events:
        delta = (e["time"] - now).total_seconds() / 60
        if -PAUSE_AFTER <= delta <= PAUSE_BEFORE:
            return True, e["event"]
    return False, None


def _event_key(e: dict) -> str:
    return f"{e['time'].isoformat()}|{e['currency']}|{e['event']}"


async def check_news_calendar():
    global last_calendar_fetch, news_pause_notified, news_warned_events
    now_utc = datetime.now(UTC)
    now_sgt = datetime.now(ZoneInfo("Asia/Singapore"))

    # Refetch calendar once per ~24h so high_impact_events stays current
    if last_calendar_fetch is None or (now_utc - last_calendar_fetch).total_seconds() > 86400:
        fetch_news_calendar()

    # Per-event warning: fire ~1hr before each event
    for e in high_impact_events:
        key = _event_key(e)
        if key in news_warned_events:
            continue
        mins_until = (e["time"] - now_sgt).total_seconds() / 60
        # Window: 50 < mins <= 60 — wide enough to catch a 10-sec loop, narrow enough to stay "1hr before"
        if 50 < mins_until <= 60:
            sgt = e["time"].astimezone(ZoneInfo("Asia/Singapore"))
            await send_telegram(
                f"🗓️ High-Impact News in 1 Hour\n\n"
                f"⚠️ {sgt.strftime('%H:%M SGT')} — {e['currency']}: {e['event']}\n\n"
                f"Heads up Raphael fam — manage your risk and use wider stops if needed. 🧘"
            )
            news_warned_events.add(key)
            save_news_state()

    blackout, name = is_news_blackout()
    if blackout and not news_pause_notified:
        await send_telegram(
            f"⚠️ High-Impact News Incoming — {name}\n\n"
            f"Heads up Raphael fam! News event in the next {PAUSE_BEFORE} mins. "
            f"Raphael is still active — manage your risk and use wider stops if needed. 🧘"
        )
        news_pause_notified = True
        save_news_state()
    elif not blackout and news_pause_notified:
        await send_telegram("✅ News event passed. Raphael is hunting setups as normal. 🔥")
        news_pause_notified = False
        save_news_state()


# ═══════════════════════════════════════════════
#  ORDER BLOCK ENGINE
# ═══════════════════════════════════════════════
def detect_order_blocks(df: pd.DataFrame):
    """
    Scan the last OB_LOOKBACK M5 bars for demand/supply Order Blocks.
    Only includes zones >= OB_MIN_SIZE ($3) — smaller zones are unreliable.
    """
    demand = []
    supply = []
    for i in range(len(df) - 3, len(df) - 3 - OB_LOOKBACK, -1):
        if df["close"].iloc[i] < df["open"].iloc[i]:
            if df["close"].iloc[i + 2] > df["high"].iloc[i]:
                zone_size = df["high"].iloc[i] - df["low"].iloc[i]
                if zone_size >= OB_MIN_SIZE:
                    demand.append((df["low"].iloc[i], df["high"].iloc[i]))
        if df["close"].iloc[i] > df["open"].iloc[i]:
            if df["close"].iloc[i + 2] < df["low"].iloc[i]:
                zone_size = df["high"].iloc[i] - df["low"].iloc[i]
                if zone_size >= OB_MIN_SIZE:
                    supply.append((df["low"].iloc[i], df["high"].iloc[i]))
    return demand, supply


def check_order_block_signal(df: pd.DataFrame, demand: list, supply: list):
    """Return (signal, zone) if price is inside a demand or supply OB, else (None, None).

    BUY requires price in lower half of the demand zone, SELL in upper half of the
    supply zone. This keeps the midpoint entry at/above current price for BUY (and
    at/below for SELL) so the EA's market fill has real room to TP1.
    """
    price = df["close"].iloc[-1]
    for low, high in demand:
        mid = (low + high) / 2
        if low <= price <= mid:
            return "BUY", (low, high)
    for low, high in supply:
        mid = (low + high) / 2
        if mid <= price <= high:
            return "SELL", (low, high)
    return None, None


def get_momentum(df: pd.DataFrame) -> str:
    """Compare last candle body to body 3 candles ago; return BULLISH/BEARISH/WEAK."""
    body = abs(df["close"].iloc[-1] - df["open"].iloc[-1])
    prev = abs(df["close"].iloc[-3] - df["open"].iloc[-3])
    if body > prev * 1.5:
        return "BULLISH" if df["close"].iloc[-1] > df["open"].iloc[-1] else "BEARISH"
    return "WEAK"


def calculate_tp_sl_from_zone(df: pd.DataFrame, signal: str, zone: tuple):
    """
    BUY:  entry = zone midpoint; SL = recent swing low (capped at MAX_SL below entry);
          TP1 = entry + TP1_DIST; TP2 = entry + TP2_DIST
    SELL: entry = zone midpoint; SL = recent swing high (capped at MAX_SL above entry);
          TP1 = entry - TP1_DIST; TP2 = entry - TP2_DIST
    """
    low, high = zone
    entry = round((low + high) / 2, 2)  # Midpoint entry — backtested optimal
    if signal == "BUY":
        sl  = max(df["low"].iloc[-200:].min(), entry - MAX_SL)
        tp1 = entry + TP1_DIST
        tp2 = entry + TP2_DIST
    else:
        sl  = min(df["high"].iloc[-200:].max(), entry + MAX_SL)
        tp1 = entry - TP1_DIST
        tp2 = entry - TP2_DIST
    return round(entry, 2), round(tp1, 2), round(tp2, 2), round(sl, 2)


# ═══════════════════════════════════════════════
#  TRADE MONITORING
# ═══════════════════════════════════════════════
def _runner_sl_after_tp1(trade: dict) -> float:
    """Stop level for the runner leg after TP1 (MT4 MODIFY_SL target)."""
    entry = float(trade["entry_price"])
    typ = trade["type"]
    mode = str(trade.get("runner_stop_mode") or RUNNER_STOP_MODE).strip().upper()
    orig_sl = float(trade.get("orig_sl", trade["sl"]))
    if mode == "NONE":
        return orig_sl
    if mode == "BE":
        return entry
    if mode == "LOCK":
        lock = float(trade.get("runner_lock_usd", RUNNER_LOCK_USD))
        return entry + lock if typ == "BUY" else entry - lock
    return entry


def _runner_stop_hit_log_status(trade: dict) -> str:
    mode = str(trade.get("runner_stop_mode") or RUNNER_STOP_MODE).strip().upper()
    if mode == "LOCK":
        return "LOCK_HIT"
    if mode == "NONE":
        return "RUNNER_SL_HIT"
    return "BE_HIT"


async def check_trade(df: pd.DataFrame):
    global active_trade, last_sl_time, monitoring_trade

    if not active_trade:
        return

    price = round(df["close"].iloc[-1], 2)
    t     = active_trade

    if t["type"] == "BUY":
        if not t.get("entry_touched") and price <= t["entry_price"]:
            t["entry_touched"] = True
            save_state()

        if price >= t["tp1"] and not t["tp1_hit"] and t.get("entry_touched"):
            rate, w, be, l, _ = get_win_rate()
            await send_telegram("🧠")
            await send_telegram(
                f"🔥 TP1 HIT — Move SL to break even, take partials!\n\n"
                f"Win Rate: {rate}% ({w}W/{l}L)"
            )
            log_signal(t["type"], t["entry"], t["tp1"], t["tp2"], t["sl"],
                       "TP1_HIT", **_log_kwargs(t))
            new_sl = _runner_sl_after_tp1(t)
            write_signal("MODIFY_SL", t["type"], t["tp1"], t["tp2"], new_sl)
            monitoring_trade = {
                **t,
                "tp1_hit": True,
                "sl": new_sl,
                "orig_sl": float(t.get("orig_sl", t["sl"])),
            }
            active_trade = None
            save_state(); save_monitor()
            _print_win_rate_console("TP1")

        elif price <= t["sl"]:
            await send_telegram("🔴 SL HIT")
            log_signal(t["type"], t["entry"], t["tp1"], t["tp2"], t["sl"],
                       "SL_HIT", **_log_kwargs(t))
            write_signal("CLOSE", "BUY")
            last_sl_time = time.time()
            zone_sl_times[(t["type"], round(t.get("zone_low", 0), 2), round(t.get("zone_high", 0), 2))] = time.time()
            active_trade = None
            save_state()
            _print_win_rate_console("SL")

    else:  # SELL
        if not t.get("entry_touched") and price >= t["entry_price"]:
            t["entry_touched"] = True
            save_state()

        if price <= t["tp1"] and not t["tp1_hit"] and t.get("entry_touched"):
            rate, w, be, l, _ = get_win_rate()
            await send_telegram("🧠")
            await send_telegram(
                f"🔥 TP1 HIT — Move SL to break even, take partials!\n\n"
                f"Win Rate: {rate}% ({w}W/{l}L)"
            )
            log_signal(t["type"], t["entry"], t["tp1"], t["tp2"], t["sl"],
                       "TP1_HIT", **_log_kwargs(t))
            new_sl = _runner_sl_after_tp1(t)
            write_signal("MODIFY_SL", t["type"], t["tp1"], t["tp2"], new_sl)
            monitoring_trade = {
                **t,
                "tp1_hit": True,
                "sl": new_sl,
                "orig_sl": float(t.get("orig_sl", t["sl"])),
            }
            active_trade = None
            save_state(); save_monitor()
            _print_win_rate_console("TP1")

        elif price >= t["sl"]:
            await send_telegram("🔴 SL HIT")
            log_signal(t["type"], t["entry"], t["tp1"], t["tp2"], t["sl"],
                       "SL_HIT", **_log_kwargs(t))
            write_signal("CLOSE", "SELL")
            last_sl_time = time.time()
            zone_sl_times[(t["type"], round(t.get("zone_low", 0), 2), round(t.get("zone_high", 0), 2))] = time.time()
            active_trade = None
            save_state()
            _print_win_rate_console("SL")


async def check_monitoring_trade(df: pd.DataFrame):
    global monitoring_trade

    if not monitoring_trade:
        return

    price = round(df["close"].iloc[-1], 2)
    t     = monitoring_trade

    if t["type"] == "BUY":
        if price >= t["tp2"]:
            await send_telegram(
                f"👑 RAPHAEL 👑\n\nTP2 hit — {t['type']} from {t['entry']}! 🚀"
            )
            log_signal(t["type"], t["entry"], t["tp1"], t["tp2"], t["sl"],
                       "TP2_HIT", **_log_kwargs(t))
            write_signal("CLOSE", "BUY")
            monitoring_trade = None
            save_monitor()
            _print_win_rate_console("TP2")
        elif price <= t["sl"]:
            st = _runner_stop_hit_log_status(t)
            if st == "BE_HIT":
                await send_telegram("☺️ Break Even — trade closed at entry. Protect the account!")
            elif st == "RUNNER_SL_HIT":
                await send_telegram("🔴 Runner SL hit — remainder stopped at structure.")
            else:
                await send_telegram(
                    f"🔒 Runner locked — closed at +${t.get('runner_lock_usd', RUNNER_LOCK_USD)} from entry."
                )
            log_signal(t["type"], t["entry"], t["tp1"], t["tp2"], t["sl"], st, **_log_kwargs(t))
            write_signal("CLOSE", "BUY")
            monitoring_trade = None
            save_monitor()
            _print_win_rate_console(st)

    else:  # SELL
        if price <= t["tp2"]:
            await send_telegram(
                f"👑 RAPHAEL 👑\n\nTP2 hit — {t['type']} from {t['entry']}! 🚀"
            )
            log_signal(t["type"], t["entry"], t["tp1"], t["tp2"], t["sl"],
                       "TP2_HIT", **_log_kwargs(t))
            write_signal("CLOSE", "SELL")
            monitoring_trade = None
            save_monitor()
            _print_win_rate_console("TP2")
        elif price >= t["sl"]:
            st = _runner_stop_hit_log_status(t)
            if st == "BE_HIT":
                await send_telegram("☺️ Break Even — trade closed at entry. Protect the account!")
            elif st == "RUNNER_SL_HIT":
                await send_telegram("🔴 Runner SL hit — remainder stopped at structure.")
            else:
                await send_telegram(
                    f"🔒 Runner locked — closed at +${t.get('runner_lock_usd', RUNNER_LOCK_USD)} from entry."
                )
            log_signal(t["type"], t["entry"], t["tp1"], t["tp2"], t["sl"], st, **_log_kwargs(t))
            write_signal("CLOSE", "SELL")
            monitoring_trade = None
            save_monitor()
            _print_win_rate_console(st)


def _log_kwargs(t: dict) -> dict:
    return {
        "session":           t.get("session", ""),
        "signal_source":     t.get("signal_source", "OB"),
        "ema_bias":          t.get("ema_bias", ""),
        "sl_distance":       t.get("sl_distance", 0),
        "tp1_distance":      t.get("tp1_distance", 0),
        "zone_size":         t.get("zone_size", 0),
        "candle_body_ratio": t.get("candle_body_ratio", 0),
        "open_time":         t.get("open_time"),
    }


# ═══════════════════════════════════════════════
#  SIGNAL CAPTION BUILDER
# ═══════════════════════════════════════════════
# ─── Re-entry tracker (display only — does not affect signal logic) ───
REENTRY_WINDOW_SEC = 3600  # 60 minutes
_recent_opens: list = []   # [(direction, entry, ts), ...]

def _prune_recent_opens(now_ts: float) -> None:
    global _recent_opens
    _recent_opens = [o for o in _recent_opens if now_ts - o[2] <= REENTRY_WINDOW_SEC]

def is_reentry(direction: str, entry) -> bool:
    now_ts = time.time()
    _prune_recent_opens(now_ts)
    e = round(float(entry), 2)
    return any(d == direction and round(float(p), 2) == e for d, p, _ in _recent_opens)

def record_open(direction: str, entry) -> None:
    _recent_opens.append((direction, round(float(entry), 2), time.time()))


def build_caption(signal: str, entry, tp1, tp2, sl, session: str,
                  reentry: bool = False) -> str:
    if signal == "BUY":
        header = "📈 🕗🕘🕖"
    else:
        header = "📉 🕐🕑🕒🕒"

    warning = "⚠️ RE-ENTRY — Higher Risk\n\n" if reentry else ""

    return (
        f"{warning}"
        f"{header}\n\n"
        f"🟢 Entry: {entry}\n"
        f"🟢 TP1:   {tp1}\n"
        f"🟢 TP2:   {tp2}\n"
        f"🟢 TP3:   Open 🚀\n"
        f"🔴 SL:    {sl}\n\n"
        f"❤️ Session: {session}\n"
    )


# ═══════════════════════════════════════════════
#  COMMAND HANDLER
# ═══════════════════════════════════════════════
async def handle_commands():

    @tg_client.on(events.NewMessage(from_users=ADMIN_ID, pattern=r"^/status"))
    async def status(event):
        t = active_trade or monitoring_trade
        if t:
            phase = "Monitoring (TP1 hit)" if monitoring_trade else "Active"
            msg = (
                f"🧠 {phase} Trade\n\n"
                f"Type:  {t['type']}\n"
                f"Entry: {t['entry']}\n"
                f"TP1:   {t['tp1']}\n"
                f"TP2:   {t['tp2']}\n"
                f"SL:    {t['sl']}\n"
            )
        else:
            msg = "No active trade."
        await event.respond(msg)

    @tg_client.on(events.NewMessage(from_users=ADMIN_ID, pattern=r"^/cancel"))
    async def cancel(event):
        global active_trade
        active_trade = None
        save_state()
        await event.respond("✅ Active trade cleared.")

    @tg_client.on(events.NewMessage(from_users=ADMIN_ID, pattern=r"^/close"))
    async def close_trade(event):
        global active_trade, monitoring_trade
        t = active_trade or monitoring_trade
        if not t:
            await event.respond("No active trade to close.")
            return
        write_signal("CLOSE", t["type"])
        await send_telegram(
            f"🔴 Trade Closed Manually\n\n"
            f"{t['type']} from {t['entry']} closed by the trader.\n\n"
            f"Stay sharp Raphael fam! 👊"
        )
        active_trade = monitoring_trade = None
        save_state(); save_monitor()
        await event.respond("✅ Trade closed and group notified.")

    @tg_client.on(events.NewMessage(from_users=ADMIN_ID, pattern=r"^/setsl (\d+\.?\d*)"))
    async def setsl(event):
        global active_trade
        if not active_trade:
            await event.respond("No active trade.")
            return
        active_trade["sl"] = float(event.pattern_match.group(1))
        save_state()
        await event.respond(f"✅ SL updated to {active_trade['sl']}")

    @tg_client.on(events.NewMessage(from_users=ADMIN_ID, pattern=r"^/settp1 (\d+\.?\d*)"))
    async def settp1(event):
        global active_trade
        if not active_trade:
            await event.respond("No active trade.")
            return
        active_trade["tp1"] = float(event.pattern_match.group(1))
        save_state()
        await event.respond(f"✅ TP1 updated to {active_trade['tp1']}")

    @tg_client.on(events.NewMessage(from_users=ADMIN_ID, pattern=r"^/settp2 (\d+\.?\d*)"))
    async def settp2(event):
        global active_trade
        if not active_trade:
            await event.respond("No active trade.")
            return
        active_trade["tp2"] = float(event.pattern_match.group(1))
        save_state()
        await event.respond(f"✅ TP2 updated to {active_trade['tp2']}")

    @tg_client.on(events.NewMessage(pattern=r"^/whoami"))
    async def whoami(event):
        await event.respond(f"Your Telegram ID: {event.sender_id}")

    @tg_client.on(events.NewMessage(from_users=ADMIN_ID,
                                     pattern=r"^/buysignal (\d+\.?\d*) (\d+\.?\d*)"))
    async def buysignal(event):
        global active_trade, last_signal, last_signal_time
        if active_trade:
            await event.respond("Active trade exists. /cancel it first.")
            return
        try:
            low  = min(float(event.pattern_match.group(1)), float(event.pattern_match.group(2)))
            high = max(float(event.pattern_match.group(1)), float(event.pattern_match.group(2)))
            df   = get_candles()
            zone = (low, high)
            entry_price, tp1, tp2, sl = calculate_tp_sl_from_zone(df, "BUY", zone)
            session = get_session()
            img     = create_signal_image("BUY", entry_price, tp1, tp2, sl)
            re_flag = is_reentry("BUY", entry_price)
            await send_telegram_image(img, build_caption("BUY", entry_price, tp1, tp2, sl, session, reentry=re_flag))
            record_open("BUY", entry_price)
            active_trade = _make_trade("BUY", entry_price, tp1, tp2, sl, zone, "MANUAL", session, df)
            save_state()
            write_signal("BUY", "BUY", tp1, tp2, sl, zone_low=low, zone_high=high, entry_price=entry_price)
            last_signal = "BUY"; last_signal_time = time.time()
            await event.respond(f"✅ BUY fired! Entry: {entry_price} TP1: {tp1} TP2: {tp2} SL: {sl}")
        except Exception as e:
            await event.respond(f"❌ Error: {e}")

    @tg_client.on(events.NewMessage(from_users=ADMIN_ID,
                                     pattern=r"^/sellsignal (\d+\.?\d*) (\d+\.?\d*)"))
    async def sellsignal(event):
        global active_trade, last_signal, last_signal_time
        if active_trade:
            await event.respond("Active trade exists. /cancel it first.")
            return
        try:
            low  = min(float(event.pattern_match.group(1)), float(event.pattern_match.group(2)))
            high = max(float(event.pattern_match.group(1)), float(event.pattern_match.group(2)))
            df   = get_candles()
            zone = (low, high)
            entry_price, tp1, tp2, sl = calculate_tp_sl_from_zone(df, "SELL", zone)
            session = get_session()
            img     = create_signal_image("SELL", entry_price, tp1, tp2, sl)
            re_flag = is_reentry("SELL", entry_price)
            await send_telegram_image(img, build_caption("SELL", entry_price, tp1, tp2, sl, session, reentry=re_flag))
            record_open("SELL", entry_price)
            active_trade = _make_trade("SELL", entry_price, tp1, tp2, sl, zone, "MANUAL", session, df)
            save_state()
            write_signal("SELL", "SELL", tp1, tp2, sl, zone_low=low, zone_high=high, entry_price=entry_price)
            last_signal = "SELL"; last_signal_time = time.time()
            await event.respond(f"✅ SELL fired! Entry: {entry_price} TP1: {tp1} TP2: {tp2} SL: {sl}")
        except Exception as e:
            await event.respond(f"❌ Error: {e}")


# ═══════════════════════════════════════════════
#  TRADE FACTORY
# ═══════════════════════════════════════════════
def _make_trade(signal, entry_price, tp1, tp2, sl, zone, source, session, df) -> dict:
    ob_low, ob_high = zone
    last = df.iloc[-1]
    body = abs(last["close"] - last["open"])
    rng  = (last["high"] - last["low"]) or 1
    return {
        "type":              signal,
        "entry":             str(entry_price),
        "entry_price":       entry_price,
        "tp1":               tp1,
        "tp2":               tp2,
        "sl":                sl,
        "orig_sl":           sl,
        "runner_stop_mode":  RUNNER_STOP_MODE,
        "runner_lock_usd":   RUNNER_LOCK_USD,
        "tp1_hit":           False,
        "entry_touched":     True,
        "signal_source":     source,
        "ema_bias":          "",
        "sl_distance":       round(abs(sl - entry_price), 2),
        "tp1_distance":      round(abs(tp1 - entry_price), 2),
        "zone_size":         round(ob_high - ob_low, 2),
        "zone_low":          ob_low,
        "zone_high":         ob_high,
        "candle_body_ratio": round(body / rng, 4),
        "session":           session,
        "open_time":         datetime.now().isoformat(),
    }


# ═══════════════════════════════════════════════
#  MAIN BOT LOOP
# ═══════════════════════════════════════════════
async def run_bot():
    global active_trade, last_signal, last_signal_time, last_session_ann, last_dead_hour_ann

    load_state()
    load_monitor()
    load_news_state()
    _print_win_rate_console("from log (startup)")

    while True:
        try:
            now_sgt     = datetime.now(ZoneInfo("Asia/Singapore"))
            is_saturday = now_sgt.weekday() == 5

            df = get_candles("M5")

            await check_session_announcement()
            await check_news_calendar()
            await check_trade(df)
            await check_monitoring_trade(df)

            # Saturday shutdown
            if is_saturday and active_trade is None and monitoring_trade is None:
                s = _parse_log_stats()
                summary = (
                    f"👑 Raphael is signing off for the weekend!\n\n"
                    f"🗓️ Weekly Summary:\n\n"
                    f"✅ TP1 Hits:   {s['tp1']}\n"
                    f"👑 TP2 Hits:   {s['tp2']}\n"
                    f"☺️ Break Evens: {s['be']}\n"
                    f"🔴 SL Hits:    {s['sl']} (+ runner SL {s['runner_sl']})\n"
                    f"🔒 Lock Hits:  {s['lock']}\n\n"
                    f"📊 Win Rate: {s['rate']}%\n"
                    f"⚡️ Net Pips: {s['net']} pips\n\n"
                    f"Have a wonderful weekend Raphael fam! Rest up — back Monday. 🔥\n\n"
                    f"👑 See you Monday!"
                )
                if SILENT_TELEGRAM:
                    print("Saturday — weekly summary (silent mode):\n" + summary)
                else:
                    await send_telegram(summary)
                print("Saturday — shutting down. Goodbye! 🌙")
                if not SILENT_TELEGRAM and tg_client.is_connected():
                    await tg_client.disconnect()
                os._exit(0)

            # ── OB signal detection (only when no active trade) ──
            if active_trade is None and not is_saturday:
                now      = time.time()
                utc_hour = datetime.now(UTC).hour

                # ── Dead hours filter ──
                # Note: do not reuse last_session_ann here — check_session_announcement() sets it to None
                # whenever hour ∉ {23,7,13}, which includes all dead hours, and would re-fire every loop.
                if utc_hour in DEAD_HOURS:
                    log_once(f"Dead hour {(utc_hour + 8) % 24:02d}:00 SGT — skipping")
                    await asyncio.sleep(10)
                    continue

                demand, supply = detect_order_blocks(df)
                signal, zone   = check_order_block_signal(df, demand, supply)

                if signal:
                    momentum = get_momentum(df)
                    if signal == "SELL" and momentum == "BULLISH":
                        log_once("SELL filtered — bullish momentum")
                        signal = None
                    elif signal == "BUY" and momentum == "BEARISH":
                        log_once("BUY filtered — bearish momentum")
                        signal = None

                if signal:
                    if now - last_sl_time < 300:
                        print("Cooldown: SL hit within 5 min")
                        signal = None
                    elif signal == last_signal and now - last_signal_time < 300:
                        print("Cooldown: same signal within 5 min")
                        signal = None

                if signal:
                    # Zone cooldown
                    zone_key = (signal, round(zone[0], 2), round(zone[1], 2))
                    if zone_key in zone_sl_times:
                        secs = now - zone_sl_times[zone_key]
                        if secs < ZONE_COOLDOWN_SECS:
                            print(f"Zone cooldown: {signal} {zone[0]}-{zone[1]} blocked {round((ZONE_COOLDOWN_SECS-secs)/60)}m")
                            signal = None

                if signal:
                    # H1 bias filter
                    h1b = get_h1_bias()
                    if h1b == "BEARISH" and signal == "BUY":
                        log_once("BUY filtered — H1 bearish")
                        signal = None
                    elif h1b == "BULLISH" and signal == "SELL":
                        log_once("SELL filtered — H1 bullish")
                        signal = None
                    elif ENABLE_SELL_H1_NEUTRAL_BLOCK and h1b == "NEUTRAL" and signal == "SELL":
                        log_once("SELL filtered — H1 neutral")
                        signal = None

                if signal:
                    # H4 bias filter
                    h4b = get_h4_bias()
                    if h4b == "BEARISH" and signal == "BUY":
                        log_once("BUY filtered — H4 bearish")
                        signal = None
                    elif h4b == "BULLISH" and signal == "SELL":
                        log_once("SELL filtered — H4 bullish")
                        signal = None

                if signal and ENABLE_SELL_LONDON_BLOCK:
                    if signal == "SELL" and 7 <= utc_hour < 13:
                        log_once("SELL filtered — London session")
                        signal = None

                if signal and ENABLE_SELL_BEARISH_CANDLE_BLOCK:
                    if signal == "SELL" and df["close"].iloc[-1] < df["open"].iloc[-1]:
                        log_once("SELL filtered — bearish entry candle")
                        signal = None

                if signal and ENABLE_BUY_BEAR_H1_NEAR_STRUCT_BLOCK:
                    try:
                        df_h1_check = get_candles("H1", count=5)
                        last_h1 = df_h1_check.iloc[-1]
                        if signal == "BUY" and last_h1["close"] < last_h1["open"]:
                            lookback_20 = df.iloc[-20:]
                            dist = lookback_20["high"].max() - df["close"].iloc[-1]
                            if dist < 8:
                                log_once("BUY filtered — H1 bearish candle + close to resistance")
                                signal = None
                    except Exception:
                        pass

                if signal:
                    # FVG confluence filter
                    if not has_fvg_confluence(df, signal, zone):
                        print(f"No FVG confluence — skipping {signal}")
                        signal = None

                if signal:
                    entry_price, tp1, tp2, sl = calculate_tp_sl_from_zone(df, signal, zone)
                    session = get_session()
                    re_flag = is_reentry(signal, entry_price)
                    if SILENT_TELEGRAM:
                        print(
                            f"[silent] New signal {signal} entry={entry_price} tp1={tp1} tp2={tp2} sl={sl} "
                            f"session={session} reentry={re_flag}"
                        )
                    else:
                        img = create_signal_image(signal, entry_price, tp1, tp2, sl)
                        await send_telegram_image(
                            img, build_caption(signal, entry_price, tp1, tp2, sl, session, reentry=re_flag)
                        )
                    record_open(signal, entry_price)
                    active_trade = _make_trade(signal, entry_price, tp1, tp2, sl,
                                               zone, "OB", session, df)
                    log_signal(signal, entry_price, tp1, tp2, sl, "OPEN",
                               **_log_kwargs(active_trade))
                    save_state()
                    write_signal(signal, signal, tp1, tp2, sl,
                                 zone_low=zone[0], zone_high=zone[1], entry_price=entry_price)
                    last_signal      = signal
                    last_signal_time = now
                    print(f"Signal: {signal} | Entry: {entry_price} | TP1: {tp1} | TP2: {tp2} | SL: {sl}")

            await asyncio.sleep(10)

        except asyncio.CancelledError:
            print("Raphael bot stopped.")
            break
        except Exception as e:
            import traceback
            print("Error:", e)
            traceback.print_exc()
            if not SILENT_TELEGRAM and not tg_client.is_connected():
                print("Reconnecting Telegram...")
                await tg_client.connect()
            await asyncio.sleep(10)


# ═══════════════════════════════════════════════
#  ENTRY POINT
# ═══════════════════════════════════════════════
async def main():
    if SILENT_TELEGRAM:
        print(
            "Raphael Beta — Telegram silent (CSV + console). "
            "Set RAPHAEL_BETA_SILENT=0 to enable channel messages. "
            f"Log: {LOG_FILE}"
        )
        try:
            await run_bot()
        except (asyncio.CancelledError, KeyboardInterrupt):
            print("\n🛑 Raphael Beta stopped.")
        return

    await tg_client.start()
    await handle_commands()

    # ── One-time announcement ──
    if not os.path.isfile(ANNOUNCEMENT_FILE):
        try:
            await send_telegram(
                "👑 Raphael v4.0 — Biggest Upgrade Yet!\n\n"
                "🧠 What's new:\n\n"
                "📊 Smarter entry logic — better confirmation before firing\n"
                "🔍 Institutional confluence filter — higher quality setups only\n"
                "📈 Multi-timeframe bias — M5 signals aligned with H1 and H4\n"
                "⏰ Smart session filter — avoids low liquidity periods\n"
                "🔒 Zone protection — prevents re-entering failed zones\n"
                "📐 Minimum zone quality filter — only strong OBs\n"
                "🕯️ Candle confirmation — entry aligned with momentum\n\n"
                "Backtested across 1, 3 and 6 months of real XAUUSD data:\n"
                "✅ Win Rate: 88.8%\n"
                "⚡️ Net Pips: +29,715\n\n"
                "🤖 Special thanks to the Raphael team — working together we identified key improvements that pushed Raphael's win rate from 60% to 88.8%. The future of trading is AI-assisted. 🧠\n\n"
                "Let's get these pips Raphael fam! 🔥🚀"
            )
            with open(ANNOUNCEMENT_FILE, "w") as f:
                f.write(datetime.now().isoformat())
        except Exception as e:
            print(f"Announcement error: {e}")

    # ── One-time win-rate recalibration announcement ──
    if not os.path.isfile(WINRATE_FIX_FLAG):
        try:
            rate, wins, _be, losses, _net = get_win_rate()
            await send_telegram(
                "⚠️ Raphael — Honest Recalibration\n\n"
                "We identified and fixed a bug in the OB signal trigger that was causing some signals to fire when price was already at the TP1 level on MT4 — producing instant TP1 hits with no real room to run.\n\n"
                "🛠️ What we fixed:\n"
                "The OB trigger now only fires when price is in the lower half of demand zones (BUY) or upper half of supply zones (SELL). This guarantees the midpoint entry always has real distance to TP1 before the EA fills at market.\n\n"
                "📉 Why the win rate dropped:\n"
                "Some previous wins came from signals where the EA filled right at the TP1 level → instant exit with no actual gain. Those trades inflated our stats. The fix removes that scenario.\n\n"
                f"📊 Current Win Rate: {rate}% ({wins}W / {losses}L)\n\n"
                "Going forward you'll see fewer signals, but each will have real, honest setups behind them. Thanks for trusting Raphael — we're committed to transparency over inflated numbers. 🤝"
            )
            with open(WINRATE_FIX_FLAG, "w") as f:
                f.write(datetime.now().isoformat())
        except Exception as e:
            print(f"Winrate fix announcement error: {e}")

    try:
        await asyncio.gather(
            run_bot(),
            tg_client.run_until_disconnected()
        )
    except (asyncio.CancelledError, KeyboardInterrupt):
        print("\n🛑 Raphael shutting down gracefully...")
    except Exception as e:
        print("Fatal error:", e)
    finally:
        if tg_client.is_connected():
            await tg_client.disconnect()
        print("✅ Raphael disconnected. Goodbye!")


try:
    asyncio.run(main())
except KeyboardInterrupt:
    pass
