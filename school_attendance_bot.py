"""
Telegram Personal-Account Auto-Away Responder + Math Calculator
-----------------------------------------------
Logs in as YOUR Telegram account (not a bot) using Telethon.

FEATURES:
  - Away mode (toggle with .away / .back in Saved Messages)
  - Robot image sent before away text reply
  - Math calculator (any private chat)
  - Auto-forward from specific private chats
  - Group mirror: forward EVERYTHING from one group to another
  - Media auto-save
  - Daily digest
  - Offline status when away
  - Session keepalive (get_me every 3 days to prevent session expiry)

ENV VARS:
  TG_API_ID=
  TG_API_HASH=
  TG_SESSION_STRING=
  AWAY_MESSAGE=Hi {name}! Chalie is currently not active, will reply soon.
  AWAY_IMAGE_PATH=./away_robot.jpg
  FORWARD_TARGET=
  FORWARD_ALL_FROM=id1,id2,@username3
  FORWARD_KEYWORDS=urgent,invoice
  FORWARD_ON_MEDIA=true
  MEDIA_SAVE_DIR=./saved_media
  DIGEST_ENABLED=true
  DIGEST_TIME=20:00
  GROUP_SOURCE=  (group username or ID to mirror FROM)
  GROUP_TARGET=  (group username or ID to mirror TO)
"""

import os
import re
import math as _math
import asyncio
import threading
from datetime import datetime, date
from http.server import BaseHTTPRequestHandler, HTTPServer
from dotenv import load_dotenv
from telethon import TelegramClient, events, utils
from telethon.sessions import StringSession
from telethon.tl.types import User
from telethon.tl.functions.account import UpdateStatusRequest

load_dotenv()

API_ID = int(os.environ["TG_API_ID"])
API_HASH = os.environ["TG_API_HASH"]
SESSION_STRING = os.environ.get("TG_SESSION_STRING", "")

AWAY_MESSAGE = os.environ.get(
    "AWAY_MESSAGE",
    "Hi {name}! Chalie is currently not active, will reply soon."
)

AWAY_IMAGE_PATH = os.environ.get("AWAY_IMAGE_PATH", "./away_robot.jpg")

# --- Auto-forward config ---
FORWARD_TARGET = os.environ.get("FORWARD_TARGET", "")
FORWARD_KEYWORDS = [
    k.strip().lower() for k in os.environ.get("FORWARD_KEYWORDS", "").split(",") if k.strip()
]
FORWARD_ON_MEDIA = os.environ.get("FORWARD_ON_MEDIA", "false").lower() == "true"
FORWARD_ALL_FROM_RAW = [
    x.strip() for x in os.environ.get("FORWARD_ALL_FROM", "").split(",") if x.strip()
]

# --- Forward exclude list (never forward messages from these IDs/usernames) ---
FORWARD_EXCLUDE_RAW = [
    x.strip() for x in os.environ.get("FORWARD_EXCLUDE", "609517172").split(",") if x.strip()
]

# --- Group mirror config ---
GROUP_SOURCE = os.environ.get("GROUP_SOURCE", "")
GROUP_TARGET = os.environ.get("GROUP_TARGET", "")

# --- Media organizer config ---
MEDIA_SAVE_DIR = os.environ.get("MEDIA_SAVE_DIR", "./saved_media")

# --- Daily digest config ---
DIGEST_ENABLED = os.environ.get("DIGEST_ENABLED", "false").lower() == "true"
DIGEST_TIME = os.environ.get("DIGEST_TIME", "20:00")

# In-memory state
is_away = False
already_replied_to = set()
forward_target_entity = None
forward_all_from_ids = set()
forward_exclude_ids = set()   # never forward from these IDs
group_source_id = None       # normalized "marked" chat id, matches event.chat_id
group_target_entity = None
daily_stats = {}
last_digest_date = None

client = TelegramClient(StringSession(SESSION_STRING), API_ID, API_HASH)


# --- Session keepalive (prevents Telegram from expiring the session) ----------

async def session_keepalive_loop():
    """
    Call get_me() every 3 days to prevent Telegram from expiring the session
    due to "terminate inactive sessions". This is the fix for weekly disconnects.
    """
    INTERVAL = 3 * 24 * 60 * 60  # 3 days in seconds
    while True:
        await asyncio.sleep(INTERVAL)
        try:
            me = await client.get_me()
            print(f"[keepalive] Session active — logged in as {me.first_name} (ID {me.id})")
        except Exception as e:
            print(f"[keepalive] get_me() failed: {e}")


# --- Offline-status control ---

async def set_telegram_offline(offline: bool):
    try:
        await client(UpdateStatusRequest(offline=offline))
        print(f"[presence] Set account -> {'offline' if offline else 'online'}")
    except Exception as e:
        print(f"[presence] Failed: {e}")


async def offline_keepalive_loop():
    while True:
        if is_away:
            await set_telegram_offline(True)
        await asyncio.sleep(30)


# --- Math calculator (scientific, full order of operations) ---

import math as _math

# Safe names allowed inside eval
_SAFE_GLOBALS = {
    "__builtins__": {},
    "abs": abs, "round": round, "pow": pow,
    "sqrt": _math.sqrt, "log": _math.log, "log10": _math.log10,
    "log2": _math.log2, "sin": _math.sin, "cos": _math.cos,
    "tan": _math.tan, "asin": _math.asin, "acos": _math.acos,
    "atan": _math.atan, "atan2": _math.atan2,
    "floor": _math.floor, "ceil": _math.ceil,
    "pi": _math.pi, "e": _math.e,
    "factorial": _math.factorial,
}


def _clean_expr(expr: str) -> str:
    """Normalise an expression string so Python eval can handle it."""
    expr = expr.strip()
    # Remove thousands-separating commas (e.g. 1,000 → 1000)
    expr = re.sub(r'(\d),(\d)', r'\1\2', expr)
    # Replace common alternate symbols
    expr = expr.replace("×", "*").replace("÷", "/").replace("^", "**")
    # Replace 'x' used as multiply only when surrounded by digits/spaces
    expr = re.sub(r'(?<=[\d\s])[xX](?=[\d\s])', '*', expr)
    return expr


def _safe_eval(expr: str):
    """Evaluate a mathematical expression safely. Returns (result, error_str)."""
    try:
        result = eval(expr, _SAFE_GLOBALS, {})   # noqa: S307
        return result, None
    except ZeroDivisionError:
        return None, "Division by zero"
    except Exception as e:
        return None, str(e)


def _fmt(value) -> str:
    """Format a number nicely — no trailing .0 for integers."""
    if isinstance(value, float) and value.is_integer():
        return f"{int(value):,}"
    if isinstance(value, float):
        # Up to 10 significant digits, strip trailing zeros
        s = f"{value:.10g}"
        return s
    return f"{value:,}"


def parse_and_calculate(text: str):
    """
    Scientific calculator.

    Handles:
      • Full order-of-operations:  3+6*5+9  →  42
      • Multi-line with per-line results + grand total
      • Optional label prefix:  "Apples = 3*5"
      • Functions: sqrt(), sin(), log(), factorial(), …
      • Constants: pi, e
      • Exponent: 2^10 or 2**10
      • Percent: 200*15% → 30  (% converted to /100)
    """
    lines = text.strip().splitlines()
    results = []
    grand_total = 0.0
    found_any = False

    for raw_line in lines:
        raw_line = raw_line.strip()
        if not raw_line:
            continue

        # Try to split "Label = expression" or just "expression"
        label = ""
        expr_part = raw_line
        label_match = re.match(r'^([^=\d(]+?)\s*=\s*(.+)$', raw_line)
        if label_match:
            possible_label = label_match.group(1).strip()
            possible_expr = label_match.group(2).strip()
            # Only treat as label if the left side has no digits (avoid "3+2 = ?" style)
            if not re.search(r'\d', possible_label):
                label = possible_label
                expr_part = possible_expr

        # Normalise percent signs before cleaning  e.g. 15% → 0.15
        expr_part = re.sub(r'(\d+(?:\.\d+)?)\s*%', lambda m: str(float(m.group(1)) / 100), expr_part)

        clean = _clean_expr(expr_part)

        # Only try eval if the expression contains a digit or known constant
        if not re.search(r'[\d]|pi|e\b', clean):
            results.append(raw_line)
            continue

        value, err = _safe_eval(clean)
        if err is not None or value is None:
            results.append(raw_line)
            continue

        found_any = True
        try:
            grand_total += float(value)
        except (TypeError, ValueError):
            pass

        fmt_val = _fmt(value)
        if label:
            results.append(f"{label} = {expr_part} = {fmt_val}")
        else:
            results.append(f"{expr_part} = {fmt_val}")

    if not found_any:
        return None

    if len([r for r in results if "=" in r]) > 1:
        # Only show grand total when there are multiple calculations
        results.append("")
        results.append(f"Total = {_fmt(grand_total)}")

    return "\n".join(results)


# --- Helpers ---

def sender_display_name(sender) -> str:
    if isinstance(sender, User):
        name = " ".join(filter(None, [sender.first_name, sender.last_name])).strip()
        if not name:
            name = sender.username or f"id{sender.id}"
        return name
    return getattr(sender, "title", None) or f"id{getattr(sender, 'id', 'unknown')}"


def build_away_message(sender) -> str:
    if isinstance(sender, User) and sender.first_name:
        name = sender.first_name
    else:
        name = sender_display_name(sender)
    try:
        return AWAY_MESSAGE.format(name=name)
    except (KeyError, IndexError):
        return AWAY_MESSAGE


def safe_filename_part(name: str) -> str:
    return re.sub(r'[^a-zA-Z0-9_-]', "_", name)[:40]


# --- Resolve helpers ---

async def resolve_from_dialogs(target_id: int):
    """
    Search dialogs for a match by either the bare entity id OR the
    normalized 'marked' peer id (the form Telethon uses for event.chat_id,
    e.g. -100xxxxxxxxxx for supergroups/channels).
    """
    try:
        async for dialog in client.iter_dialogs():
            if dialog.entity.id == target_id or utils.get_peer_id(dialog.entity) == target_id:
                return dialog.entity
    except Exception as e:
        print(f"[resolve] Error: {e}")
    return None


async def resolve_any_chat(value: str):
    """
    Resolve a username or numeric ID (bare or marked/-100 form) to an entity.
    """
    value = value.strip()
    if not value:
        raise ValueError("empty value")

    if value.lstrip("-").isdigit():
        raw_id = int(value)
        found = await resolve_from_dialogs(raw_id)
        if found:
            return found
        try:
            return await client.get_entity(raw_id)
        except Exception:
            pass
        if str(raw_id).startswith("-100"):
            try:
                bare_id = int(str(raw_id)[4:])
                return await client.get_entity(bare_id)
            except Exception:
                pass
        raise ValueError(f"could not resolve ID {raw_id}")

    return await client.get_entity(value)


async def resolve_forward_target():
    global forward_target_entity
    if not FORWARD_TARGET:
        print("[forward] No FORWARD_TARGET set.")
        return
    try:
        forward_target_entity = await resolve_any_chat(FORWARD_TARGET)
        print(f"[forward] Target resolved: {sender_display_name(forward_target_entity)}")
    except Exception as e:
        print(f"[forward] Could not resolve FORWARD_TARGET: {e}")


async def resolve_forward_all_from():
    global forward_all_from_ids
    if not FORWARD_ALL_FROM_RAW:
        print("[forward] No FORWARD_ALL_FROM set.")
        return
    print(f"[forward] Resolving {len(FORWARD_ALL_FROM_RAW)} FORWARD_ALL_FROM entries...")
    for entry in FORWARD_ALL_FROM_RAW:
        try:
            if entry.lstrip("-").isdigit():
                target_id = int(entry)
                entity = await resolve_from_dialogs(target_id)
                forward_all_from_ids.add(target_id)
                name = sender_display_name(entity) if entity else str(target_id)
                print(f"[forward] ✅ {name} → ID {target_id}")
            else:
                entity = await client.get_entity(entry)
                forward_all_from_ids.add(entity.id)
                print(f"[forward] ✅ {entry} → ID {entity.id}")
        except Exception as e:
            print(f"[forward] ❌ Could not resolve '{entry}': {e}")
    print(f"[forward] Active IDs: {forward_all_from_ids}")


async def resolve_forward_exclude():
    global forward_exclude_ids
    for entry in FORWARD_EXCLUDE_RAW:
        try:
            if entry.lstrip("-").isdigit():
                forward_exclude_ids.add(int(entry))
                print(f"[forward] 🚫 Excluded ID: {entry}")
            else:
                entity = await client.get_entity(entry)
                forward_exclude_ids.add(entity.id)
                print(f"[forward] 🚫 Excluded: {entry} → ID {entity.id}")
        except Exception as e:
            print(f"[forward] ❌ Could not resolve exclude '{entry}': {e}")


async def resolve_group_mirror():
    """
    Resolves GROUP_SOURCE / GROUP_TARGET. Stores group_source_id as the
    normalized 'marked' peer id for direct comparison against event.chat_id.
    """
    global group_source_id, group_target_entity
    if not GROUP_SOURCE or not GROUP_TARGET:
        print("[mirror] GROUP_SOURCE or GROUP_TARGET not set — mirror disabled.")
        return
    try:
        source_entity = await resolve_any_chat(GROUP_SOURCE)
        group_source_id = utils.get_peer_id(source_entity)
        print(f"[mirror] ✅ Source: {getattr(source_entity, 'title', GROUP_SOURCE)} → chat_id {group_source_id}")
    except Exception as e:
        print(f"[mirror] ❌ Could not resolve GROUP_SOURCE: {e}")
        return
    try:
        group_target_entity = await resolve_any_chat(GROUP_TARGET)
        print(f"[mirror] ✅ Target: {getattr(group_target_entity, 'title', GROUP_TARGET)}")
    except Exception as e:
        print(f"[mirror] ❌ Could not resolve GROUP_TARGET: {e}")


# --- Handlers ---

@client.on(events.NewMessage(outgoing=True, chats="me"))
async def toggle_handler(event):
    global is_away, already_replied_to
    text = (event.raw_text or "").strip().lower()
    if text == ".away":
        is_away = True
        already_replied_to.clear()
        await set_telegram_offline(True)
        await event.reply(f"✅ Away mode ON ({datetime.now().strftime('%H:%M')})")
        print("[state] Away mode enabled")
    elif text == ".back":
        is_away = False
        already_replied_to.clear()
        await set_telegram_offline(False)
        await event.reply(f"✅ Away mode OFF ({datetime.now().strftime('%H:%M')})")
        print("[state] Away mode disabled")


@client.on(events.NewMessage(incoming=True))
async def message_handler(event):
    """Handle ALL incoming messages — private and group."""

    # ── GROUP MIRROR ──────────────────────────────────────────────────────
    if not event.is_private:
        if group_source_id and group_target_entity:
            if event.chat_id == group_source_id:
                try:
                    await client.forward_messages(group_target_entity, event.message)
                    print(f"[mirror] ✅ Forwarded group message to target")
                except Exception as e:
                    print(f"[mirror] ❌ Failed: {e}")
        return

    # ── PRIVATE CHAT ──────────────────────────────────────────────────────
    sender = await event.get_sender()
    if sender is None or getattr(sender, "bot", False):
        return

    sender_id = sender.id
    message_text = event.raw_text or ""

    # Daily stats
    name = sender_display_name(sender)
    entry = daily_stats.setdefault(sender_id, {"name": name, "count": 0})
    entry["count"] += 1
    entry["name"] = name

    # Media organizer
    if event.message.media:
        try:
            os.makedirs(MEDIA_SAVE_DIR, exist_ok=True)
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            prefix = f"{safe_filename_part(name)}_{ts}"
            saved_path = await client.download_media(
                event.message, file=os.path.join(MEDIA_SAVE_DIR, prefix)
            )
            if saved_path:
                print(f"[media] Saved from {name} -> {saved_path}")
        except Exception as e:
            print(f"[media] Failed to save media from {name}: {e}")

    # Auto-forward
    should_forward = False
    if forward_target_entity is not None and sender_id not in forward_exclude_ids:
        if forward_all_from_ids and sender_id in forward_all_from_ids:
            should_forward = True
            print(f"[forward] Matched FORWARD_ALL_FROM: {name}")
        elif event.message.media and FORWARD_ON_MEDIA:
            should_forward = True
        elif FORWARD_KEYWORDS and message_text:
            if any(kw in message_text.lower() for kw in FORWARD_KEYWORDS):
                should_forward = True
    elif sender_id in forward_exclude_ids:
        print(f"[forward] Skipped (excluded): {name}")

    if should_forward:
        try:
            await client.forward_messages(forward_target_entity, event.message)
            print(f"[forward] ✅ Forwarded from {name}")
        except Exception as e:
            print(f"[forward] ❌ Failed: {e}")

    # Math calculator
    calc_result = parse_and_calculate(message_text)
    if calc_result:
        await event.reply(calc_result)
        print(f"[math] Replied with calculation to {name}")
        return

    # Auto-away reply
    if not is_away:
        return
    if sender_id in already_replied_to:
        return

    # Send robot image first, then away text
    if AWAY_IMAGE_PATH and os.path.exists(AWAY_IMAGE_PATH):
        try:
            await client.send_file(sender_id, AWAY_IMAGE_PATH)
        except Exception as e:
            print(f"[auto-reply] Failed to send image to {name}: {e}")
    else:
        print(f"[auto-reply] Image not found ({AWAY_IMAGE_PATH}), skipping.")

    await event.reply(build_away_message(sender))
    already_replied_to.add(sender_id)
    print(f"[auto-reply] Sent image + away message to {name}")


# --- Daily digest ---

async def digest_loop():
    global last_digest_date, daily_stats
    if not DIGEST_ENABLED:
        print("[digest] Disabled.")
        return
    try:
        target_hour, target_minute = (int(p) for p in DIGEST_TIME.split(":"))
    except Exception:
        print(f"[digest] Invalid DIGEST_TIME. Disabled.")
        return
    print(f"[digest] Will send at {DIGEST_TIME} each day.")
    while True:
        now = datetime.now()
        today = date.today()
        if now.hour == target_hour and now.minute == target_minute and last_digest_date != today:
            await send_digest()
            last_digest_date = today
        await asyncio.sleep(30)


async def send_digest():
    if not daily_stats:
        summary = "📊 Daily digest: no incoming private messages today."
    else:
        lines = ["📊 Daily digest — incoming private messages:"]
        total = 0
        for stats in sorted(daily_stats.values(), key=lambda s: -s["count"]):
            lines.append(f"  • {stats['name']}: {stats['count']}")
            total += stats["count"]
        lines.append("")
        lines.append(f"Total messages: {total}")
        lines.append(f"Unique senders: {len(daily_stats)}")
        summary = "\n".join(lines)
    try:
        await client.send_message("me", summary)
        print("[digest] Sent daily digest")
    except Exception as e:
        print(f"[digest] Failed: {e}")
    daily_stats.clear()


# --- HTTP keep-alive ---

class PingHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-type", "text/plain")
        self.end_headers()
        status = "AWAY" if is_away else "ACTIVE"
        fwd_ids = ",".join(str(i) for i in forward_all_from_ids) or "none"
        mirror = f"{group_source_id}→{getattr(group_target_entity,'id','?')}" if group_source_id else "disabled"
        self.wfile.write(
            f"OK - status: {status} - forward_all_from: {fwd_ids} - mirror: {mirror}".encode()
        )

    def log_message(self, format, *args):
        pass


def start_ping_server():
    port = int(os.environ.get("PORT", 10000))
    server = HTTPServer(("0.0.0.0", port), PingHandler)
    print(f"[keep-alive] Ping server on port {port}")
    server.serve_forever()


# --- Main ---

async def main():
    threading.Thread(target=start_ping_server, daemon=True).start()
    print("Logging in...")
    await client.start()
    print("Logged in. Listening for messages.")
    print("Send '.away' or '.back' to your Saved Messages to toggle.")

    if not SESSION_STRING:
        print("\n[!] Save this to TG_SESSION_STRING:\n")
        print(client.session.save())
        print()

    await resolve_forward_target()
    await resolve_forward_all_from()
    await resolve_forward_exclude()
    await resolve_group_mirror()

    if is_away:
        await set_telegram_offline(True)

    asyncio.create_task(offline_keepalive_loop())
    asyncio.create_task(session_keepalive_loop())   # <-- prevents session expiry

    if DIGEST_ENABLED:
        asyncio.create_task(digest_loop())

    await client.run_until_disconnected()


if __name__ == "__main__":
    asyncio.run(main())
