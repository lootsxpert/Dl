import asyncio
import base64
import hashlib
import hmac
import html
import logging
import json
import random
import re
import string
import time
import ssl
from io import BytesIO
from datetime import datetime, timedelta, timezone
from urllib.parse import quote_plus, unquote_plus, urljoin, urlparse

from pyrogram import Client, filters, raw, utils
from pyrogram.types import InlineKeyboardMarkup, InlineKeyboardButton, WebAppInfo
from pyrogram.errors import (
    UserNotParticipant,
    ChatAdminRequired,
    ChatWriteForbidden,
    FloodWait,
    UserIsBlocked,
    InputUserDeactivated,
    PeerIdInvalid,
    MessageNotModified,
    WebpageMediaEmpty,
)
from pyrogram.enums import ChatMemberStatus
import aiohttp
import os
from dotenv import load_dotenv
from quart import Quart
from quart import Response, request

try:
    import certifi
except Exception:
    certifi = None

try:
    from motor.motor_asyncio import AsyncIOMotorClient
except Exception:
    AsyncIOMotorClient = None

load_dotenv()
BOT_BOOT_TIME_UTC = datetime.now(timezone.utc)

# Telegram allows bots to upload up to 2 GB; override via TELEGRAM_MAX_UPLOAD_MB if needed.
TELEGRAM_MAX_UPLOAD_MB = float(os.getenv("TELEGRAM_MAX_UPLOAD_MB", "2048"))
LIMIT_FREE_REQUESTS = 3
UNLOCK_TOKEN_TTL_SECONDS = 60 * 60  # 1 hour to use the unlock token
STREAM_TOKEN_TTL_SECONDS = 15 * 60  # 15 minutes
MAX_LINKS_PER_MESSAGE = 3
UNLOCK_PROMPT_COOLDOWN_SECONDS = 90
INVALID_LINK_REPLY_COOLDOWN_SECONDS = 120
DISKWALA_DOMAIN_KEYWORDS = ("diskwala",)
SUPPORTED_DISKWALA_DOMAINS = ("diskwala.com", "www.diskwala.com")
def _parse_admin_ids() -> set[int]:
    ids: set[int] = set()
    for env_name in ("ADMIN_USER_IDS", "ADMIN_USER_ID"):
        for part in os.getenv(env_name, "").split(","):
            part = part.strip()
            if part.lstrip("-").isdigit():
                ids.add(int(part))
    return ids or {641770277}


ADMIN_USER_IDS = _parse_admin_ids()
ADMIN_USER_ID = min(ADMIN_USER_IDS)  # primary admin, kept for legacy single-admin call sites
ADMIN_CONTACT_BOT = os.getenv("ADMIN_CONTACT_BOT", "iMovies_contact_bot").lstrip("@")
AUTO_DELETE_SECONDS = 45 * 60  # 45 minutes
PREMIUM_DAILY_DOWNLOADS = int(os.getenv("PREMIUM_DAILY_DOWNLOADS", "50"))
PAYMENT_TOKEN_TTL_SECONDS = 10 * 60
PAYMENT_SESSION_TTL_SECONDS = 15 * 60
PREMIUM_END_REMINDER_WINDOW_HOURS = int(os.getenv("PREMIUM_END_REMINDER_WINDOW_HOURS", "6"))

# ===== CONFIG =====
API_ID = int(os.getenv('API_ID'))
API_HASH = os.getenv('API_HASH')
BOT_TOKEN = os.getenv('BOT_TOKEN')
DISKWALA_API_KEY = os.getenv("DISKWALA_API_KEY", "").strip()
DISKWALA_API_BASE = os.getenv("DISKWALA_API_BASE", "http://teradl.kingx.dev:8080").strip().rstrip("/")
SHORTLINK_API = os.getenv('SHORTLINK_API')
BOT_USERNAME = os.getenv('BOT_USERNAME')
PUBLIC_BASE_URL = os.getenv("PUBLIC_BASE_URL", "")
PUBLIC_BASE_URL = PUBLIC_BASE_URL.strip().strip('"').strip("'").rstrip("/")  # e.g. https://your-domain.com
FORCE_SUB_CHANNEL = os.getenv("FORCE_SUB_CHANNEL", "")  # your updates channel
MONGO_URI = os.getenv("MONGO_URI", "").strip()
MONGO_DB_NAME = os.getenv("MONGO_DB_NAME", "").strip()
RAZORPAY_KEY_ID = os.getenv("RAZORPAY_KEY_ID", "").strip()
RAZORPAY_KEY_SECRET = os.getenv("RAZORPAY_KEY_SECRET", "").strip()
RAZORPAY_WEBHOOK_SECRET = os.getenv("RAZORPAY_WEBHOOK_SECRET", "").strip()

PREMIUM_PLANS = {
    "day": {"label": "1 Day", "amount_inr": 5, "days": 1, "stars": 10},
    "week": {"label": "1 Week", "amount_inr": 30, "days": 7, "stars": 60},
    "month": {"label": "1 Month", "amount_inr": 100, "days": 30, "stars": 200},
    "quarter": {"label": "3 Months", "amount_inr": 250, "days": 90, "stars": 500},
    "quota50": {
        "label": "Quota Top-up (+50 today)",
        "amount_inr": 5,
        "days": 0,
        "stars": 10,
        "quota_add": 50,
        "is_addon": True,
    },
}

app = Client(
    "diskwala_downloader_bot",
    api_id=API_ID,
    api_hash=API_HASH,
    bot_token=BOT_TOKEN
)

bot = Quart(__name__)
# bot.config['PROVIDE_AUTOMATIC_OPTIONS'] = True


def _sanitize_bot_key(raw: str, fallback_idx: int = 0) -> str:
    cleaned = re.sub(r"[^a-z0-9_]", "_", (raw or "").lower())
    return cleaned or f"bot_{fallback_idx}"
logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)
# bot_info =  app.get_me()
# bot_username = bot_info.username

# ===== MEMORY STORAGE (TEMP ONLY) =====
# user_id -> {"remaining": int, "date": "YYYY-MM-DD"}
user_data: dict[int, dict] = {}
# user_id -> asyncio.Lock() (prevents race conditions on credits)
user_locks: dict[int, asyncio.Lock] = {}
# unlock_token -> {"user_id": int, "used": bool, "expires_at": float}
tokens: dict[str, dict] = {}
# stream_token -> {"url": str, "expires_at": float}
stream_tokens: dict[str, dict] = {}
# file_token -> pending Get File request metadata
file_tokens: dict[str, dict] = {}
payment_tokens: dict[str, dict] = {}

mongo_client = None
mongo_db = None
users_col = None
payments_col = None
premium_reminder_task = None
_force_sub_warned = False
# broadcast job_id -> {"cancel": asyncio.Event, "admin_id": int}
_broadcast_jobs: dict[str, dict] = {}
# transfer job_id -> {"cancel": asyncio.Event, "user_id": int}
_file_transfer_jobs: dict[str, dict] = {}

# In-memory admin toggles (not persisted; reset on restart)
QUOTA_ENABLED = True  # /shortlink_on|off - when False, free users must buy premium after free quota
FREE_MODE_ENABLED = False  # /freemode_on|off - when True, bot is free for everyone
SENDFILE_ENABLED = True  # /sendfile_on|off - when False, Get File (Premium) shows admin-disabled popup

# In-memory per-API usage/health counters (not persisted; reset on restart).
# api_key -> {attempts, success, fail, consecutive_fails, last_ok_at, last_fail_at, last_error}
_api_stats: dict[str, dict] = {}


def _record_api_result(api_key: str, ok: bool, error: str = "") -> None:
    st = _api_stats.setdefault(api_key, {
        "attempts": 0, "success": 0, "fail": 0, "consecutive_fails": 0,
        "last_ok_at": None, "last_fail_at": None, "last_error": "",
    })
    st["attempts"] += 1
    if ok:
        st["success"] += 1
        st["consecutive_fails"] = 0
        st["last_ok_at"] = _now_ts()
    else:
        st["fail"] += 1
        st["consecutive_fails"] += 1
        st["last_fail_at"] = _now_ts()
        if error:
            st["last_error"] = str(error)[:200]


def _ssl_context_with_certifi() -> ssl.SSLContext | None:
    if certifi is None:
        return None
    return ssl.create_default_context(cafile=certifi.where())


def _today_utc_str() -> str:
    return str(datetime.now(timezone.utc).date())


def _now_ts() -> float:
    return time.time()


def _cleanup_expired_tokens() -> None:
    now = _now_ts()
    for t in [k for k, v in tokens.items() if v.get("expires_at", 0) <= now]:
        tokens.pop(t, None)
    for t in [k for k, v in stream_tokens.items() if v.get("expires_at", 0) <= now]:
        stream_tokens.pop(t, None)
    for t in [k for k, v in payment_tokens.items() if v.get("expires_at", 0) <= now]:
        payment_tokens.pop(t, None)
    for t in [k for k, v in file_tokens.items() if v.get("expires_at", 0) <= now]:
        file_tokens.pop(t, None)


def _utc_now() -> datetime:
    return datetime.now(timezone.utc)


def _is_premium_enabled() -> bool:
    return bool(users_col is not None)


def _is_razorpay_enabled() -> bool:
    return bool(RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET)


async def _get_premium_until(user_id: int) -> datetime | None:
    if users_col is None:
        return None
    doc = await users_col.find_one({"user_id": int(user_id)}, {"premium_until": 1})
    if not doc:
        return None
    ts = doc.get("premium_until")
    if isinstance(ts, datetime):
        if ts.tzinfo is None:
            ts = ts.replace(tzinfo=timezone.utc)
        return ts
    return None


def _is_admin_user(user_id: int) -> bool:
    return int(user_id) in ADMIN_USER_IDS


async def _is_premium_user(user_id: int) -> bool:
    premium_until = await _get_premium_until(user_id)
    return bool(premium_until and premium_until > _utc_now())


async def _has_premium_access(user_id: int) -> bool:
    """Premium subscribers and env-configured admins get premium-only features."""
    if _is_admin_user(user_id):
        return True
    return await _is_premium_user(user_id)


async def _upsert_user_profile(user, bot_key: str) -> None:
    if users_col is None or not user:
        return
    now = _utc_now()
    await users_col.update_one(
        {"user_id": int(user.id)},
        {
            "$set": {
                "user_id": int(user.id),
                "username": user.username,
                "first_name": user.first_name,
                "last_name": user.last_name,
                "is_bot": bool(getattr(user, "is_bot", False)),
                "updated_at": now,
                "last_seen_at": now,
                f"bots.{bot_key}.last_seen_at": now,
                f"bots.{bot_key}.bot_username": bot_key,
            },
            "$setOnInsert": {
                "created_at": now,
            },
            "$addToSet": {"bot_keys": bot_key},
        },
        upsert=True,
    )


async def _get_quota_state(user_id: int, daily_limit: int) -> dict:
    today = _today_utc_str()
    limit = int(daily_limit)
    if users_col is None:
        user = user_data.get(user_id, {"remaining": limit, "date": today, "limit": limit})
        if user["date"] != today or int(user.get("limit", limit)) != limit:
            user["date"] = today
            user["remaining"] = limit
            user["limit"] = limit
            user_data[user_id] = user
        return user

    doc = await users_col.find_one({"user_id": int(user_id)}, {"quota": 1})
    quota = (doc or {}).get("quota") or {}
    current_date = quota.get("date")
    current_limit = int(quota.get("limit", limit))
    remaining = int(quota.get("remaining", limit))

    if current_date != today or current_limit != limit:
        quota = {"date": today, "remaining": limit, "limit": limit}
        await users_col.update_one(
            {"user_id": int(user_id)},
            {"$set": {"user_id": int(user_id), "quota": quota, "updated_at": _utc_now()}},
            upsert=True,
        )
        return quota

    return {"date": current_date, "remaining": remaining, "limit": current_limit}


async def _apply_premium_plan(user_id: int, plan_key: str, payment_id: str = "") -> datetime:
    plan = PREMIUM_PLANS[plan_key]
    now = _utc_now()
    current = await _get_premium_until(user_id)
    base = current if current and current > now else now
    new_until = base + timedelta(days=plan["days"])
    if users_col is not None:
        await users_col.update_one(
            {"user_id": int(user_id)},
            {"$set": {
                "user_id": int(user_id),
                "premium_until": new_until,
                "updated_at": now,
                "last_plan": plan_key,
                "last_payment_id": payment_id,
                "premium_reminders": {},
                "premium_tracking_enabled": True,
            }},
            upsert=True,
        )
    return new_until


async def _apply_quota_addon(user_id: int, plan_key: str) -> int:
    plan = PREMIUM_PLANS[plan_key]
    quota_add = int(plan.get("quota_add", 0))
    if quota_add <= 0:
        return 0
    is_premium = await _is_premium_user(user_id)
    daily_limit = PREMIUM_DAILY_DOWNLOADS if is_premium else LIMIT_FREE_REQUESTS
    lock = _get_user_lock(user_id)
    async with lock:
        state = await _get_quota_state(user_id, daily_limit=daily_limit)
        new_remaining = int(state.get("remaining", 0)) + quota_add
        if users_col is None:
            state["remaining"] = new_remaining
            user_data[user_id] = state
        else:
            await users_col.update_one(
                {"user_id": int(user_id)},
                {"$set": {"quota.remaining": new_remaining, "updated_at": _utc_now()}},
                upsert=True,
            )
    return quota_add


async def _apply_purchase(user_id: int, plan_key: str, payment_id: str = "") -> str:
    plan = PREMIUM_PLANS[plan_key]
    if int(plan.get("days", 0)) > 0:
        until = await _apply_premium_plan(user_id, plan_key, payment_id=payment_id)
        return f"✅ Premium activated till {until.strftime('%Y-%m-%d %H:%M UTC')}"
    if int(plan.get("quota_add", 0)) > 0:
        added = await _apply_quota_addon(user_id, plan_key)
        return f"✅ Quota top-up successful. Added +{added} downloads for today."
    return "✅ Purchase processed."


def _format_user_name(user_obj=None, fallback: str = "") -> str:
    if user_obj is None:
        return fallback or "Unknown"
    first = (getattr(user_obj, "first_name", "") or "").strip()
    last = (getattr(user_obj, "last_name", "") or "").strip()
    full = (f"{first} {last}").strip()
    if full:
        return full
    username = (getattr(user_obj, "username", "") or "").strip()
    if username:
        return f"@{username}"
    return fallback or "Unknown"


def _force_sub_join_url() -> str:
    raw = (FORCE_SUB_CHANNEL or "").strip()
    if not raw:
        return ""
    if raw.startswith(("http://", "https://")):
        return raw
    if raw.startswith("@"):
        return f"https://t.me/{raw.lstrip('@')}"
    if raw.startswith("-100"):
        return ""
    return f"https://t.me/{raw}"


def _force_sub_chat_ref() -> str | int | None:
    raw = (FORCE_SUB_CHANNEL or "").strip()
    if not raw:
        return None
    if raw.startswith("-100") and raw[1:].isdigit():
        return int(raw)
    if raw.startswith("@"):
        return raw
    if raw.startswith(("http://", "https://")):
        parsed = urlparse(raw)
        path = (parsed.path or "").strip("/")
        if not path:
            return None
        if path.startswith("+"):
            return None
        return f"@{path.split('/')[0]}"
    if raw.startswith("+"):
        return None
    return f"@{raw}"


async def _notify_admin(client: Client, text: str) -> None:
    for admin_id in ADMIN_USER_IDS:
        try:
            await client.send_message(admin_id, text, disable_web_page_preview=True)
        except Exception:
            pass


async def _notify_premium_purchase(client: Client, user_id: int, plan_key: str, until: datetime, payment_id: str = "",
                                   source: str = "") -> None:
    plan = PREMIUM_PLANS.get(plan_key) or {}
    user_name = "Unknown"
    user_uname = ""
    try:
        u = await client.get_users(int(user_id))
        user_name = _format_user_name(u)
        if getattr(u, "username", None):
            user_uname = f"@{u.username}"
    except Exception:
        pass
    await _notify_admin(
        client,
        (
            "💰 Premium purchased\n\n"
            f"User: {user_name}\n"
            f"Username: {user_uname or 'N/A'}\n"
            f"User ID: `{int(user_id)}`\n"
            f"Plan: {plan.get('label', plan_key)}\n"
            f"Amount: ₹{plan.get('amount_inr', 'N/A')}\n"
            f"Valid till: {until.strftime('%Y-%m-%d %H:%M UTC')}\n"
            f"Payment ID: {payment_id or 'N/A'}\n"
            f"Source: {source or 'unknown'}"
        ),
    )


async def _notify_purchase(client: Client, user_id: int, plan_key: str, payment_id: str = "", source: str = "") -> None:
    plan = PREMIUM_PLANS.get(plan_key) or {}
    is_addon = bool(plan.get("is_addon"))
    if is_addon:
        user_name = "Unknown"
        user_uname = ""
        try:
            u = await client.get_users(int(user_id))
            user_name = _format_user_name(u)
            if getattr(u, "username", None):
                user_uname = f"@{u.username}"
        except Exception:
            pass
        await _notify_admin(
            client,
            (
                "💰 Quota add-on purchased\n\n"
                f"User: {user_name}\n"
                f"Username: {user_uname or 'N/A'}\n"
                f"User ID: `{int(user_id)}`\n"
                f"Plan: {plan.get('label', plan_key)}\n"
                f"Amount: ₹{plan.get('amount_inr', 'N/A')} / ⭐️{plan.get('stars', 'N/A')}\n"
                f"Payment ID: {payment_id or 'N/A'}\n"
                f"Source: {source or 'unknown'}"
            ),
        )
        return
    until = await _get_premium_until(user_id)
    if until:
        await _notify_premium_purchase(client, user_id, plan_key, until, payment_id=payment_id, source=source)


def _format_ago(ts: float | None) -> str:
    if not ts:
        return "never"
    return f"{_format_duration(_now_ts() - ts)} ago"


def _api_status_text() -> str:
    labels = [
        ("diskwala", "DiskWala API"),
    ]
    lines = ["🔌 API Health & Usage"]
    for key, label in labels:
        st = _api_stats.get(key)
        if not st or st["attempts"] == 0:
            lines.append(f"⚪ {label}: not used yet")
            continue
        cf = st["consecutive_fails"]
        icon = "🟢" if cf == 0 else ("🟡" if cf < 3 else "🔴")
        rate = (st["success"] / st["attempts"] * 100) if st["attempts"] else 0.0
        line = (
            f"{icon} {label}\n"
            f"   Calls: {st['attempts']} | OK: {st['success']} | Fail: {st['fail']} ({rate:.0f}% success)\n"
            f"   Last OK: {_format_ago(st['last_ok_at'])} | Last fail: {_format_ago(st['last_fail_at'])}"
        )
        if cf > 0 and st.get("last_error"):
            line += f"\n   Last error: {st['last_error']}"
        lines.append(line)
    return "\n".join(lines)


async def _status_text(bot_key: str) -> str:
    api_text = _api_status_text()
    if users_col is None:
        total_users = len(user_data)
        return (
            "📊 Bot Status\n\n"
            f"Total users: {total_users}\n"
            "Premium users: DB not enabled\n"
            f"In-memory users today: {total_users}\n\n"
            f"Toggles: quota={'on' if QUOTA_ENABLED else 'off'} | "
            f"freemode={'on' if FREE_MODE_ENABLED else 'off'} | "
            f"sendfile={'on' if SENDFILE_ENABLED else 'off'}\n\n"
            f"{api_text}"
        )
    now = _utc_now()
    total_users = await users_col.count_documents({"bot_keys": bot_key})
    premium_users = await users_col.count_documents({"bot_keys": bot_key, "premium_until": {"$gt": now}})
    expired_premium_users = await users_col.count_documents({"bot_keys": bot_key, "premium_until": {"$lte": now}})
    active_today = await users_col.count_documents({f"bots.{bot_key}.last_seen_at": {"$gte": now - timedelta(days=1)}})
    return (
        "📊 Bot Status\n\n"
        f"Total users: {total_users}\n"
        f"Premium active users: {premium_users}\n"
        f"Premium expired users: {expired_premium_users}\n"
        f"Active users (last 24h): {active_today}\n\n"
        f"Toggles: quota={'on' if QUOTA_ENABLED else 'off'} | "
        f"freemode={'on' if FREE_MODE_ENABLED else 'off'} | "
        f"sendfile={'on' if SENDFILE_ENABLED else 'off'}\n\n"
        f"{api_text}"
    )


async def _razorpay_auth_header() -> dict:
    token = base64.b64encode(f"{RAZORPAY_KEY_ID}:{RAZORPAY_KEY_SECRET}".encode()).decode()
    return {"Authorization": f"Basic {token}", "Content-Type": "application/json"}


async def _send_stars_invoice(client: Client, chat_id: int, user_id: int, plan_key: str, plan: dict) -> None:
    stars_amount = int(plan.get("stars") or 0)
    if stars_amount <= 0:
        raise RuntimeError("Stars amount not configured for this plan")
    invoice_payload = f"stars:{user_id}:{plan_key}:{int(_now_ts())}"
    start_parameter = f"stars_{plan_key}_{int(_now_ts())}"
    prices = [raw.types.LabeledPrice(label=plan["label"], amount=stars_amount)]
    invoice = raw.types.Invoice(currency="XTR", prices=prices)
    media = raw.types.InputMediaInvoice(
        title=f"DiskWala DL - {plan['label']}",
        description=f"Buy {plan['label']} using Telegram Stars",
        invoice=invoice,
        payload=invoice_payload.encode("utf-8"),
        provider="",
        provider_data=raw.types.DataJSON(data="{}"),
        start_param=start_parameter,
    )
    if payments_col is not None:
        await payments_col.update_one(
            {"pay_ref": invoice_payload},
            {"$set": {
                "pay_ref": invoice_payload,
                "user_id": int(user_id),
                "plan_key": plan_key,
                "status": "created",
                "created_at": _utc_now(),
                "source": "create:stars",
                "currency": "XTR",
                "amount": int(stars_amount),
            }},
            upsert=True,
        )
    await client.invoke(
        raw.functions.messages.SendMedia(
            peer=await client.resolve_peer(chat_id),
            media=media,
            message="",
            random_id=client.rnd_id(),
        )
    )


async def _process_stars_payment(
    client: Client,
    user_id: int,
    payload: str,
    currency: str,
    total_amount: int,
    payment_id: str,
) -> None:
    if (currency or "").upper() != "XTR":
        return
    parts = (payload or "").split(":")
    if len(parts) < 4 or parts[0] != "stars":
        return
    payload_user = int(parts[1] or 0)
    plan_key = parts[2]
    if plan_key not in PREMIUM_PLANS:
        return
    effective_user_id = int(user_id) if int(user_id or 0) > 0 else int(payload_user or 0)
    if effective_user_id <= 0:
        return
    if int(user_id or 0) > 0 and payload_user > 0 and int(user_id) != int(payload_user):
        # Keep processing with payload owner, but report mismatch for audit.
        await report_error(
            client,
            "stars_user_mismatch",
            RuntimeError("stars user mismatch"),
            extra={"user_id": user_id, "payload_user": payload_user, "plan_key": plan_key},
        )
        effective_user_id = int(payload_user)
    if payments_col is not None:
        by_payload_paid = await payments_col.find_one(
            {"pay_ref": payload, "status": "paid"},
            {"_id": 1}
        )
        if by_payload_paid:
            return
    expected = int(PREMIUM_PLANS[plan_key].get("stars", 0))
    if int(total_amount) != expected:
        await client.send_message(effective_user_id, "❌ Stars amount mismatch. Please contact support.")
        await report_error(
            client,
            "stars_payment_amount_mismatch",
            RuntimeError("stars amount mismatch"),
            extra={"user_id": effective_user_id, "plan_key": plan_key, "amount": total_amount, "expected": expected},
        )
        return
    if not payment_id:
        payment_id = f"stars_{int(_now_ts())}"
    if payments_col is not None:
        existing = await payments_col.find_one({"payment_id": payment_id, "status": "paid"}, {"_id": 1})
        if existing:
            await client.send_message(effective_user_id, "✅ Payment already processed.")
            return
        await payments_col.update_one(
            {"pay_ref": payload},
            {"$set": {
                "pay_ref": payload,
                "payment_id": payment_id,
                "user_id": int(effective_user_id),
                "plan_key": plan_key,
                "status": "paid",
                "paid_at": _utc_now(),
                "source": "telegram_stars",
                "currency": "XTR",
                "amount": int(total_amount),
            }},
            upsert=True,
        )
        await payments_col.update_one(
            {"payment_id": payment_id},
            {"$set": {
                "payment_id": payment_id,
                "user_id": int(effective_user_id),
                "plan_key": plan_key,
                "status": "paid",
                "paid_at": _utc_now(),
                "source": "telegram_stars",
                "currency": "XTR",
                "amount": int(total_amount),
            }},
            upsert=True,
        )
    result_text = await _apply_purchase(effective_user_id, plan_key, payment_id=payment_id)
    await client.send_message(effective_user_id, result_text)
    await _notify_purchase(client, effective_user_id, plan_key, payment_id=payment_id, source="telegram_stars")


def _extract_user_id_from_service_message(msg) -> int:
    uid = utils.get_raw_peer_id(getattr(msg, "from_id", None))
    if uid:
        return int(uid)
    uid = utils.get_raw_peer_id(getattr(msg, "peer_id", None))
    return int(uid or 0)


async def _process_stars_payment_sent_fallback(client: Client, msg, action) -> None:
    user_id = _extract_user_id_from_service_message(msg)
    if not user_id or payments_col is None:
        return
    amount = int(getattr(action, "total_amount", 0) or 0)
    # Fallback for MTProto variants where payload is not present in the service action.
    session_doc = await payments_col.find_one(
        {
            "user_id": int(user_id),
            "source": "create:stars",
            "status": {"$in": ["created", "pending"]},
            "amount": amount,
        },
        sort=[("created_at", -1)],
    )
    if not session_doc:
        return
    payload = str(session_doc.get("pay_ref") or "")
    if not payload:
        return
    payment_id = f"stars_fallback_{int(getattr(msg, 'id', 0) or 0)}_{int(_now_ts())}"
    await _process_stars_payment(
        client,
        user_id,
        payload,
        getattr(action, "currency", "XTR"),
        amount,
        payment_id,
    )


async def _create_razorpay_order(user_id: int, plan_key: str, pay_token: str) -> dict:
    plan = PREMIUM_PLANS[plan_key]
    payload = {
        "amount": int(plan["amount_inr"]) * 100,
        "currency": "INR",
        "receipt": f"tg_{user_id}_{plan_key}_{int(_now_ts())}",
        "notes": {
            "user_id": str(user_id),
            "plan_key": plan_key,
            "payment_token": pay_token,
        },
    }
    headers = await _razorpay_auth_header()
    async with aiohttp.ClientSession() as session:
        async with session.post("https://api.razorpay.com/v1/orders", headers=headers,
                                data=json.dumps(payload)) as resp:
            body = await resp.text()
            if resp.status >= 400:
                raise RuntimeError(f"Razorpay order error: {resp.status} {body[:300]}")
            return json.loads(body)


async def _create_razorpay_payment_link(user_id: int, plan_key: str, pay_ref: str) -> dict:
    plan = PREMIUM_PLANS[plan_key]
    expires_at = int(_now_ts() + PAYMENT_SESSION_TTL_SECONDS)
    payload = {
        "amount": int(plan["amount_inr"]) * 100,
        "currency": "INR",
        "accept_partial": False,
        "description": f"DiskWala DL Premium - {plan['label']}",
        "reference_id": f"tg_{user_id}_{plan_key}_{int(_now_ts())}",
        "expire_by": expires_at,
        "notify": {"sms": False, "email": False},
        "reminder_enable": False,
        "notes": {
            "user_id": str(user_id),
            "plan_key": plan_key,
            "pay_ref": pay_ref,
        },
    }
    headers = await _razorpay_auth_header()
    async with aiohttp.ClientSession() as session:
        async with session.post("https://api.razorpay.com/v1/payment_links", headers=headers,
                                data=json.dumps(payload)) as resp:
            body = await resp.text()
            if resp.status < 400:
                return json.loads(body)
            # Some Razorpay accounts reject expire_by for short windows; retry once without it.
            if "expire_by" in body.lower():
                payload.pop("expire_by", None)
                async with session.post("https://api.razorpay.com/v1/payment_links", headers=headers,
                                        data=json.dumps(payload)) as retry_resp:
                    retry_body = await retry_resp.text()
                    if retry_resp.status < 400:
                        return json.loads(retry_body)
                    raise RuntimeError(f"Razorpay payment-link error: {retry_resp.status} {retry_body[:300]}")
            raise RuntimeError(f"Razorpay payment-link error: {resp.status} {body[:300]}")


async def _create_razorpay_upi_qr(user_id: int, plan_key: str, pay_ref: str) -> dict:
    plan = PREMIUM_PLANS[plan_key]
    close_at = int(_now_ts() + PAYMENT_SESSION_TTL_SECONDS)
    payload = {
        "type": "upi_qr",
        "usage": "single_use",
        "fixed_amount": True,
        "payment_amount": int(plan["amount_inr"]) * 100,
        "close_by": close_at,
        "description": f"DiskWala DL Premium - {plan['label']}",
        "notes": {
            "user_id": str(user_id),
            "plan_key": plan_key,
            "pay_ref": pay_ref,
        },
    }
    headers = await _razorpay_auth_header()
    async with aiohttp.ClientSession() as session:
        async with session.post("https://api.razorpay.com/v1/payments/qr_codes", headers=headers,
                                data=json.dumps(payload)) as resp:
            body = await resp.text()
            if resp.status < 400:
                return json.loads(body)
            # Some merchants/accounts may not support close_by on UPI QR; retry once without it.
            if "close_by" in body.lower():
                payload.pop("close_by", None)
                async with session.post("https://api.razorpay.com/v1/payments/qr_codes", headers=headers,
                                        data=json.dumps(payload)) as retry_resp:
                    retry_body = await retry_resp.text()
                    if retry_resp.status < 400:
                        return json.loads(retry_body)
                    raise RuntimeError(f"Razorpay UPI-QR error: {retry_resp.status} {retry_body[:300]}")
            raise RuntimeError(f"Razorpay UPI-QR error: {resp.status} {body[:300]}")


async def _download_qr_image_for_upload(image_url: str, pay_ref: str) -> BytesIO:
    if not image_url:
        raise RuntimeError("Missing QR image URL")
    timeout = aiohttp.ClientTimeout(total=20)
    headers = {
        "User-Agent": "Mozilla/5.0 (compatible; DiskWalaDLBot/1.0)",
        "Accept": "image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8",
    }
    async with aiohttp.ClientSession(timeout=timeout, headers=headers) as session:
        async with session.get(image_url) as resp:
            body = await resp.read()
            if resp.status >= 400:
                text = body[:300].decode("utf-8", errors="ignore")
                raise RuntimeError(f"QR image download failed: {resp.status} {text}")
            content_type = (resp.headers.get("content-type") or "").lower()
            if not body:
                raise RuntimeError("QR image download returned empty response")
            if "image" not in content_type and not image_url.lower().endswith((".png", ".jpg", ".jpeg", ".webp")):
                raise RuntimeError(f"QR image URL returned non-image content-type: {content_type or 'unknown'}")

    qr_file = BytesIO(body)
    qr_file.name = f"upi_qr_{pay_ref}.png"
    qr_file.seek(0)
    return qr_file


async def _get_razorpay_payment_link(payment_link_id: str) -> dict:
    headers = await _razorpay_auth_header()
    async with aiohttp.ClientSession() as session:
        async with session.get(f"https://api.razorpay.com/v1/payment_links/{payment_link_id}", headers=headers) as resp:
            body = await resp.text()
            if resp.status >= 400:
                raise RuntimeError(f"Razorpay payment-link status error: {resp.status} {body[:300]}")
            return json.loads(body)


async def _get_razorpay_qr(qr_code_id: str) -> dict:
    headers = await _razorpay_auth_header()
    async with aiohttp.ClientSession() as session:
        async with session.get(f"https://api.razorpay.com/v1/payments/qr_codes/{qr_code_id}", headers=headers) as resp:
            body = await resp.text()
            if resp.status >= 400:
                raise RuntimeError(f"Razorpay QR status error: {resp.status} {body[:300]}")
            return json.loads(body)


async def _cancel_razorpay_payment_link(payment_link_id: str) -> None:
    if not payment_link_id:
        return
    headers = await _razorpay_auth_header()
    async with aiohttp.ClientSession() as session:
        async with session.post(f"https://api.razorpay.com/v1/payment_links/{payment_link_id}/cancel",
                                headers=headers) as resp:
            if resp.status >= 400 and resp.status != 400:
                body = await resp.text()
                raise RuntimeError(f"Razorpay payment-link cancel error: {resp.status} {body[:300]}")


async def _close_razorpay_qr(qr_code_id: str) -> None:
    if not qr_code_id:
        return
    headers = await _razorpay_auth_header()
    async with aiohttp.ClientSession() as session:
        async with session.post(f"https://api.razorpay.com/v1/payments/qr_codes/{qr_code_id}/close",
                                headers=headers) as resp:
            if resp.status >= 400 and resp.status != 400:
                body = await resp.text()
                raise RuntimeError(f"Razorpay QR close error: {resp.status} {body[:300]}")


async def _close_payment_session(pay_ref: str) -> None:
    if not pay_ref or payments_col is None:
        return
    session_doc = await payments_col.find_one({"pay_ref": pay_ref}, {"payment_link_id": 1, "qr_code_id": 1})
    if not session_doc:
        return
    try:
        await _cancel_razorpay_payment_link(session_doc.get("payment_link_id", ""))
    except Exception:
        pass
    try:
        await _close_razorpay_qr(session_doc.get("qr_code_id", ""))
    except Exception:
        pass


async def _close_user_active_payment_sessions(user_id: int) -> None:
    if payments_col is None:
        return
    now = _now_ts()
    cursor = payments_col.find(
        {
            "user_id": int(user_id),
            "status": {"$nin": ["paid", "expired", "cancelled", "cancelled_replaced"]},
            "expires_at": {"$gt": now},
        },
        {"pay_ref": 1}
    )
    pay_refs: list[str] = []
    async for doc in cursor:
        pay_ref = (doc or {}).get("pay_ref")
        if not pay_ref:
            continue
        pay_refs.append(pay_ref)

    if not pay_refs:
        return

    await asyncio.gather(*[_close_payment_session(ref) for ref in pay_refs], return_exceptions=True)
    await payments_col.update_many(
        {"pay_ref": {"$in": pay_refs}},
        {"$set": {"status": "cancelled_replaced", "updated_at": _utc_now()}},
    )


def _verify_razorpay_signature(order_id: str, payment_id: str, signature: str) -> bool:
    raw = f"{order_id}|{payment_id}".encode()
    digest = hmac.new(RAZORPAY_KEY_SECRET.encode(), raw, hashlib.sha256).hexdigest()
    return hmac.compare_digest(digest, signature or "")


def _is_valid_http_url(u: str) -> bool:
    if not u or not isinstance(u, str):
        return False
    u = u.strip()
    try:
        p = urlparse(u)
        return p.scheme in ("http", "https") and bool(p.netloc)
    except Exception:
        return False


def _is_valid_https_url(u: str) -> bool:
    if not _is_valid_http_url(u):
        return False
    try:
        return urlparse(u.strip()).scheme == "https"
    except Exception:
        return False


async def _is_subscribed(client: Client, user_id: int) -> bool:
    """
    Returns True if user is a member/admin/owner of FORCE_SUB_CHANNEL.
    Note: bot must be admin in the channel to read members reliably.
    """
    global _force_sub_warned
    chat_ref = _force_sub_chat_ref()
    if chat_ref is None:
        if FORCE_SUB_CHANNEL and not _force_sub_warned:
            _force_sub_warned = True
            await _notify_admin(
                client,
                (
                    "⚠️ Force-sub check is disabled because `FORCE_SUB_CHANNEL` "
                    "is an invite link. Set channel @username or numeric chat id "
                    "for membership verification."
                ),
            )
        return True
    try:
        m = await client.get_chat_member(chat_ref, user_id)
        # In channels, user may appear as RESTRICTED but still "joined".
        # Treat anything except LEFT/BANNED as subscribed.
        return m.status not in (ChatMemberStatus.LEFT, ChatMemberStatus.BANNED)
    except UserNotParticipant:
        return False
    except ChatAdminRequired:
        # If bot isn't admin, treat as not subscribed to force correct setup.
        return False
    except Exception:
        return False


def _join_markup() -> InlineKeyboardMarkup:
    join_url = os.getenv("FORCE_SUB_INVITE_URL", "") or _force_sub_join_url()
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📢 Join Updates Channel", url=join_url)],
        [InlineKeyboardButton("✅ Check Joined", callback_data="check_join")],
    ])


async def _ensure_joined(client: Client, message) -> bool:
    """
    Ensures user joined FORCE_SUB_CHANNEL. If not, prompts and returns False.
    """
    try:
        user_id = message.from_user.id
    except Exception:
        return False

    if await _is_subscribed(client, user_id):
        return True

    await message.reply(
        f"To use this bot, please join our updates channel.\n\nAfter joining, tap **Check Joined**.",
        reply_markup=_join_markup()
    )
    return False


# ===== UTIL =====
def extract_urls(message, limit: int = MAX_LINKS_PER_MESSAGE) -> list[str]:
    text = message.text or message.caption or ""
    urls = re.findall(r'(https?://\S+)', text)
    return urls[: max(0, int(limit or 0))]


def _looks_like_diskwala(url: str) -> bool:
    u = (url or "").lower()
    return any(x in u for x in DISKWALA_DOMAIN_KEYWORDS)


def _supported_diskwala_domains_text() -> str:
    return "\n".join(f"- {domain}" for domain in SUPPORTED_DISKWALA_DOMAINS)


def _is_livegram_noise(text: str) -> bool:
    if not text:
        return False
    t = text.lower()
    return ("livegram" in t) or ("you cannot forward someone" in t)


def _support_markup() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🆘 Report issue", url=f"https://t.me/{ADMIN_CONTACT_BOT}")]
    ])


def _file_caption(name: str, size_mb: float) -> str:
    size_line = f"📦 {size_mb} MB" if size_mb and size_mb > 0 else "📦 Size unknown"
    return (
        f"📁 {name}\n"
        f"{size_line}\n\n"
        f"⚠️ This file will be deleted automatically in 45 minutes (copyright)."
    )


def _file_options_caption(name: str, size_mb: float, *, has_stream: bool = False) -> str:
    size_line = f"📦 {size_mb} MB" if size_mb and size_mb > 0 else "📦 Size unknown"
    lines = [
        f"📁 {name}",
        size_line,
        "",
        "Choose an option:",
    ]
    if has_stream and PUBLIC_BASE_URL:
        lines.append("▶️ Watch Now (Free) — stream in web app")
    else:
        lines.append("▶️ Watch Now (Free) — unavailable for this file")
    lines.append("📥 Get File (Premium) — sent here (auto-deleted in 45 min)")
    if size_mb > TELEGRAM_MAX_UPLOAD_MB:
        lines.append(
            f"\n⚠️ File exceeds Telegram upload limit ({TELEGRAM_MAX_UPLOAD_MB:.0f} MB). "
            "Use Watch Now if Get File fails."
        )
    return "\n".join(lines)


def _build_file_options_markup(
    file_token: str,
    *,
    stream: str,
    name: str,
    size_mb: float,
    download_url: str,
) -> InlineKeyboardMarkup | None:
    rows = []
    if stream and PUBLIC_BASE_URL:
        stoken = create_stream_token(
            stream, name=name, size_mb=size_mb, download_url=download_url or "", quality="480p",
        )
        web_app_url = f"{PUBLIC_BASE_URL}/player/{stoken}"
        if _is_valid_https_url(web_app_url):
            rows.append([InlineKeyboardButton(
                "▶️ Watch Now (Free)",
                web_app=WebAppInfo(url=web_app_url),
            )])
    if _is_valid_http_url(download_url):
        rows.append([InlineKeyboardButton(
            "📥 Get File (Premium)",
            callback_data=f"gfile:{file_token}",
        )])
    return InlineKeyboardMarkup(rows) if rows else None


async def _send_file_options_message(
    client: Client,
    message,
    msg,
    *,
    caption: str,
    markup: InlineKeyboardMarkup,
    thumbnail: str,
) -> None:
    """Send file options; use thumbnail when valid, otherwise fall back to text-only."""
    if thumbnail and _is_valid_http_url(thumbnail):
        deleted_fetch_msg = False
        try:
            await msg.delete()
            deleted_fetch_msg = True
        except Exception:
            pass
        try:
            info = await client.send_photo(
                message.chat.id,
                photo=thumbnail.strip(),
                caption=caption,
                reply_markup=markup,
            )
            _schedule_expire_media_message(client, info.chat.id, info.id)
            return
        except (WebpageMediaEmpty, Exception):
            if deleted_fetch_msg:
                msg = None

    if msg is not None:
        try:
            await msg.edit(caption, reply_markup=markup)
            _schedule_disable_and_mark_expired(client, msg.chat.id, msg.id, is_caption=False)
            return
        except Exception:
            pass

    info = await message.reply(caption, reply_markup=markup)
    _schedule_disable_and_mark_expired(
        client, info.chat.id, info.id, is_caption=bool(getattr(info, "caption", None)),
    )


def _expired_text() -> str:
    return "🗑️ Deleted / expired after 45 minutes (copyright)."


def _schedule_delete_message(client: Client, chat_id: int, message_id: int) -> None:
    async def _runner():
        await asyncio.sleep(AUTO_DELETE_SECONDS)
        try:
            await client.delete_messages(chat_id, message_id)
        except Exception:
            pass

    asyncio.create_task(_runner())


def _schedule_delete_payment_post_in(client: Client, chat_id: int, message_id: int, delay_seconds: int) -> None:
    async def _runner():
        await asyncio.sleep(max(1, int(delay_seconds)))
        try:
            await client.delete_messages(chat_id, message_id)
        except Exception:
            pass
        try:
            await client.send_message(chat_id, "Payment link/qr code deleted")
        except Exception:
            pass

    asyncio.create_task(_runner())


def _schedule_disable_and_mark_expired(client: Client, chat_id: int, message_id: int, *, is_caption: bool) -> None:
    async def _runner():
        await asyncio.sleep(AUTO_DELETE_SECONDS)
        try:
            if is_caption:
                await client.edit_message_caption(chat_id, message_id, caption=_expired_text(), reply_markup=None)
            else:
                await client.edit_message_text(chat_id, message_id, text=_expired_text(), reply_markup=None)
        except Exception:
            pass

    asyncio.create_task(_runner())


def _schedule_expire_media_message(client: Client, chat_id: int, message_id: int) -> None:
    """
    Telegram doesn't support removing media from a message.
    For photo/thumbnail messages we delete the message after TTL and send
    an "expired" text message (without thumbnail).
    """

    async def _runner():
        await asyncio.sleep(AUTO_DELETE_SECONDS)
        try:
            await client.delete_messages(chat_id, message_id)
        except Exception:
            pass
        try:
            await client.send_message(chat_id, _expired_text())
        except Exception:
            pass

    asyncio.create_task(_runner())


def _get_user_lock(user_id: int) -> asyncio.Lock:
    lock = user_locks.get(user_id)
    if lock is None:
        lock = asyncio.Lock()
        user_locks[user_id] = lock
    return lock


async def reserve_credit(user_id: int) -> tuple[bool, bool, int]:
    """
    Atomically reserve 1 credit for this user.
    If API fails later, call refund_reserved_credit().
    """
    is_premium = await _is_premium_user(user_id)
    daily_limit = PREMIUM_DAILY_DOWNLOADS if is_premium else LIMIT_FREE_REQUESTS
    lock = _get_user_lock(user_id)
    async with lock:
        state = await _get_quota_state(user_id, daily_limit=daily_limit)
        if int(state.get("remaining", 0)) <= 0:
            return False, is_premium, daily_limit
        new_remaining = max(0, int(state.get("remaining", 0)) - 1)
        if users_col is None:
            state["remaining"] = new_remaining
            user_data[user_id] = state
        else:
            await users_col.update_one(
                {"user_id": int(user_id)},
                {"$set": {"quota.remaining": new_remaining, "updated_at": _utc_now()}},
                upsert=True,
            )
        return True, is_premium, daily_limit


async def refund_reserved_credit(user_id: int, daily_limit: int, n: int = 1) -> None:
    lock = _get_user_lock(user_id)
    async with lock:
        state = await _get_quota_state(user_id, daily_limit=daily_limit)
        new_remaining = int(state.get("remaining", 0)) + int(n)
        if users_col is None:
            state["remaining"] = new_remaining
            user_data[user_id] = state
        else:
            await users_col.update_one(
                {"user_id": int(user_id)},
                {"$set": {"quota.remaining": new_remaining, "updated_at": _utc_now()}},
                upsert=True,
            )


async def _get_plan_text_and_markup(user_id: int) -> tuple[str, InlineKeyboardMarkup | None]:
    is_premium = await _is_premium_user(user_id)
    daily_limit = PREMIUM_DAILY_DOWNLOADS if is_premium else LIMIT_FREE_REQUESTS
    state = await _get_quota_state(user_id, daily_limit=daily_limit)
    remaining = int(state.get("remaining", 0))
    freemode_note = "\n\n🎉 Free mode is activated by admin temporarily for all users. Enjoy!" if FREE_MODE_ENABLED else ""
    if is_premium:
        text = (
            "Your Account Details:\n"
            "Premium Member : ✅\n"
            f"todays limit : {remaining} Remaining"
            f"{freemode_note}"
        )
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("Contact Admin", url="https://t.me/imovies_contact_bot")]
        ])
        return text, markup

    text = (
        "Your Account Details:\n"
        "Premium Member : ❌\n"
        f"Free Downloads : Remaining {remaining}/{daily_limit} downloads"
        f"{freemode_note}"
    )
    return text, None


async def _iter_all_user_ids(bot_key: str) -> list[int]:
    if users_col is None:
        return [int(uid) for uid in user_data.keys()]
    ids: list[int] = []
    cursor = users_col.find({"bot_keys": bot_key}, {"user_id": 1, "_id": 0})
    async for doc in cursor:
        uid = doc.get("user_id")
        if isinstance(uid, int):
            ids.append(uid)
    return ids


async def _remove_user_record(user_id: int, bot_key: str) -> None:
    uid = int(user_id)
    user_data.pop(uid, None)
    user_locks.pop(uid, None)
    if users_col is not None:
        await users_col.update_one(
            {"user_id": uid},
            {"$unset": {f"bots.{bot_key}": ""}, "$pull": {"bot_keys": bot_key}},
        )
        doc = await users_col.find_one({"user_id": uid}, {"bot_keys": 1})
        if doc is not None and not (doc.get("bot_keys") or []):
            await users_col.delete_one({"user_id": uid})


def _format_duration(seconds: float) -> str:
    seconds = max(0, int(seconds))
    if seconds < 60:
        return f"{seconds}s"
    mins, secs = divmod(seconds, 60)
    if mins < 60:
        return f"{mins}m {secs}s"
    hours, mins = divmod(mins, 60)
    return f"{hours}h {mins}m {secs}s"


def _broadcast_progress_text(
    *,
    total: int,
    done: int,
    sent: int,
    failed: int,
    removed: int,
    elapsed: float,
    cancelled: bool = False,
    finished: bool = False,
) -> str:
    pct = (done / total * 100) if total else 0.0
    lines = [
        "⏹ Broadcast cancelled." if cancelled and finished else (
            "✅ Broadcast completed." if finished else "📣 Broadcast in progress..."
        ),
        "",
        f"Progress: {done}/{total} ({pct:.1f}%)",
        f"Sent: {sent}",
        f"Failed: {failed}",
        f"Removed (blocked/deleted): {removed}",
        f"Elapsed: {_format_duration(elapsed)}",
    ]
    if not finished and done > 0 and done < total:
        eta = (elapsed / done) * (total - done)
        lines.append(f"ETA: ~{_format_duration(eta)}")
    elif finished:
        lines.append(f"Time taken: {_format_duration(elapsed)}")
        if cancelled and done < total:
            lines.append(f"Not sent (cancelled): {total - done}")
        if done > 0:
            lines.append(f"Avg: {elapsed / done:.2f}s per user")
    return "\n".join(lines)


def _current_bot_username(client: Client | None = None) -> str:
    me = getattr(client, "me", None) if client is not None else None
    username = (getattr(me, "username", "") or "").strip()
    if username:
        return username.lstrip("@")

    me = getattr(app, "me", None)
    username = (getattr(me, "username", "") or "").strip()
    if username:
        return username.lstrip("@")

    return (BOT_USERNAME or "").strip().lstrip("@")


def _bot_start_url(client: Client | None, payload: str) -> str:
    username = _current_bot_username(client)
    if not username:
        return ""
    return f"https://t.me/{username}?start={quote_plus(str(payload))}"


async def _broadcast_send_one(
    client: Client,
    *,
    target_id: int,
    admin_chat_id: int,
    src_message_id: int | None,
    payload_text: str,
    bot_key: str,
) -> str:
    """
    Returns: sent | blocked | removed | failed
    """
    try:
        if src_message_id is not None:
            await client.copy_message(
                chat_id=target_id,
                from_chat_id=admin_chat_id,
                message_id=src_message_id,
                caption=payload_text or None,
            )
        else:
            await client.send_message(target_id, payload_text)
        return "sent"
    except FloodWait as e:
        await asyncio.sleep(float(e.value))
        return await _broadcast_send_one(
            client,
            target_id=target_id,
            admin_chat_id=admin_chat_id,
            src_message_id=src_message_id,
            payload_text=payload_text,
            bot_key=bot_key,
        )
    except UserIsBlocked:
        await _remove_user_record(target_id, bot_key)
        return "blocked"
    except InputUserDeactivated:
        await _remove_user_record(target_id, bot_key)
        return "removed"
    except PeerIdInvalid:
        await _remove_user_record(target_id, bot_key)
        return "removed"
    except Exception:
        return "failed"


async def _broadcast_edit_status(client: Client, chat_id: int, message_id: int, text: str, markup=None) -> None:
    try:
        await client.edit_message_text(chat_id, message_id, text, reply_markup=markup)
    except MessageNotModified:
        pass
    except Exception:
        pass


async def send_unlock_once(client: Client, message, user_id: int) -> bool:
    """
    Sends the unlock prompt at most once per cooldown window per user.
    Returns True if a prompt was sent, False if suppressed (already sent recently).
    """
    lock = _get_user_lock(user_id)
    async with lock:
        now = _now_ts()
        user = user_data.get(user_id) or {}
        last_ts = float(user.get("last_unlock_prompt_ts") or 0)
        if now - last_ts < UNLOCK_PROMPT_COOLDOWN_SECONDS:
            return False
        user["last_unlock_prompt_ts"] = now
        user_data[user_id] = user

    shortlink = await generate_shortlink(user_id, client=client)
    premium_url = _bot_start_url(client, "premium")
    await message.reply(
        f"❌ Your Current Limit reached.\n\nWatch below ad to get next {LIMIT_FREE_REQUESTS} downloads:"
        f"Apple Users: Copy Ad Link, open in browser, and fully close Telegram."
        "\n\nOr you can buy premium to get unlimited downloads.😉",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🔓 Unlock Access| Watch Ad", url=shortlink)],
            [InlineKeyboardButton("❓ How to Unlock", url="https://t.me/howdisk/3")],
            [InlineKeyboardButton("💎 Buy Premium", url=premium_url)]
        ])
    )
    return True


async def send_premium_required_once(client: Client, message, user_id: int) -> bool:
    """
    Sends the premium prompt at most once per cooldown window per user.
    Returns True if a prompt was sent, False if suppressed (already sent recently).
    """
    lock = _get_user_lock(user_id)
    async with lock:
        now = _now_ts()
        user = user_data.get(user_id) or {}
        last_ts = float(user.get("last_premium_prompt_ts") or 0)
        if now - last_ts < UNLOCK_PROMPT_COOLDOWN_SECONDS:
            return False
        user["last_premium_prompt_ts"] = now
        user_data[user_id] = user

    premium_url = _bot_start_url(client, "premium")
    await message.reply(
        f"Your {LIMIT_FREE_REQUESTS} free downloads are over for today.\n\n"
        "Ad unlock is currently disabled. Please buy premium membership to continue downloading.",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("Buy Premium", url=premium_url)],
            [InlineKeyboardButton("Contact Admin", url=f"https://t.me/{ADMIN_CONTACT_BOT}")],
        ])
    )
    return True
    await message.reply(
        f"âŒ Your {LIMIT_FREE_REQUESTS} free downloads are over for today.\n\n"
        "Ad unlock is currently disabled. Please buy premium membership to continue downloading.",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("ðŸ’Ž Buy Premium", url=premium_url)],
            [InlineKeyboardButton("Contact Admin", url=f"https://t.me/{ADMIN_CONTACT_BOT}")],
        ])
    )
    return True


async def _reply_invalid_link_once(client: Client, message, user_id: int) -> bool:
    """
    Sends invalid-link guidance at most once per cooldown window per user.
    Returns True if sent, False if suppressed.
    """
    lock = _get_user_lock(user_id)
    async with lock:
        now = _now_ts()
        user = user_data.get(user_id) or {}
        last_ts = float(user.get("last_invalid_link_ts") or 0)
        if now - last_ts < INVALID_LINK_REPLY_COOLDOWN_SECONDS:
            return False
        user["last_invalid_link_ts"] = now
        user_data[user_id] = user

    await message.reply("Send a valid DiskWala link (you can send up to 3 links at once).")
    return True


async def report_error(client: Client, where: str, err: Exception, extra: dict | None = None) -> None:
    try:
        user_line = ""
        extra = extra or {}
        user_id = extra.get("user_id")
        if user_id:
            user_name = "Unknown"
            user_uname = ""
            try:
                u = await client.get_users(int(user_id))
                user_name = _format_user_name(u)
                if getattr(u, "username", None):
                    user_uname = f"@{u.username}"
            except Exception:
                user_doc = await users_col.find_one({"user_id": int(user_id)}, {"first_name": 1, "last_name": 1,
                                                                                "username": 1}) if users_col else None
                if user_doc:
                    first = (user_doc.get("first_name") or "").strip()
                    last = (user_doc.get("last_name") or "").strip()
                    user_name = (f"{first} {last}").strip() or "Unknown"
                    if user_doc.get("username"):
                        user_uname = f"@{str(user_doc.get('username')).strip()}"
            user_line = f"\nUser: {user_name} {user_uname}".rstrip()
        extra_txt = ""
        if extra:
            extra_txt = "\n\nExtra:\n" + "\n".join([f"- {k}: {str(v)[:800]}" for k, v in extra.items()])
        await _notify_admin(
            client,
            f"❗️Bot error in `{where}`{user_line}\n\n{type(err).__name__}: {err}{extra_txt}",
        )
    except Exception:
        return


async def generate_shortlink(user_id, client: Client | None = None):
    _cleanup_expired_tokens()
    token = ''.join(random.choices(string.ascii_letters + string.digits, k=8))

    tokens[token] = {
        "user_id": user_id,
        "used": False,
        "expires_at": _now_ts() + UNLOCK_TOKEN_TTL_SECONDS,
    }

    destination = _bot_start_url(client, token)

    url = f"https://nanolinks.in/api?api={SHORTLINK_API}&url={destination}"

    async with aiohttp.ClientSession() as session:
        async with session.get(url) as resp:
            data = await resp.json()

    return data.get("shortenedUrl")


def create_stream_token(stream_url: str, name: str = "", size_mb: float = 0.0,
                         download_url: str = "", quality: str = "") -> str:
    _cleanup_expired_tokens()
    token = ''.join(random.choices(string.ascii_letters + string.digits, k=24))
    stream_tokens[token] = {
        "url": stream_url,
        "name": name,
        "size_mb": size_mb,
        "download_url": download_url,
        "quality": quality,
        "expires_at": _now_ts() + STREAM_TOKEN_TTL_SECONDS,
    }
    return token


FILE_TOKEN_TTL_SECONDS = 30 * 60  # 30 minutes to choose Get File


def create_file_token(
    link: str,
    name: str,
    size_mb: float,
    stream: str,
    user_id: int,
) -> str:
    _cleanup_expired_tokens()
    token = "".join(random.choices(string.ascii_letters + string.digits, k=16))
    file_tokens[token] = {
        "link": link,
        "name": name,
        "size_mb": size_mb,
        "stream": stream,
        "user_id": int(user_id),
        "expires_at": _now_ts() + FILE_TOKEN_TTL_SECONDS,
    }
    return token


def _transfer_progress_text(
    *,
    name: str,
    size_mb: float,
    phase: str,
    current: int,
    total: int,
    speed_bps: float,
    elapsed: float,
    cancelled: bool = False,
    finished: bool = False,
    error: str = "",
) -> str:
    size_line = f"📦 {size_mb} MB" if size_mb and size_mb > 0 else "📦 Size unknown"
    lines = [f"📁 {name}", size_line, ""]

    if cancelled and finished:
        lines.append("⏹ Transfer cancelled.")
    elif error:
        lines.append(f"❌ {error}")
    elif finished:
        lines.append("✅ File sent. It will be deleted in 45 minutes.")
    else:
        lines.append(f"⏳ {phase}...")
        if total > 0:
            pct = min(100.0, (current / total) * 100)
            lines.append(f"Progress: {_human_size(current)} / {_human_size(total)} ({pct:.1f}%)")
        elif current > 0:
            lines.append(f"Transferred: {_human_size(current)}")
        if speed_bps > 0:
            lines.append(f"Speed: {_human_size(speed_bps)}/s")
        if total > 0 and current > 0 and current < total and speed_bps > 0:
            eta = (total - current) / speed_bps
            lines.append(f"ETA: ~{_format_duration(eta)}")
        lines.append(f"Elapsed: {_format_duration(elapsed)}")

    return "\n".join(lines)


class TransferCancelled(Exception):
    pass


async def download_file_with_progress(
    url: str,
    path: str,
    *,
    cancel_event: asyncio.Event,
    total_bytes: int = 0,
    on_progress=None,
) -> None:
    timeout = aiohttp.ClientTimeout(total=None, sock_connect=30, sock_read=120)
    async with aiohttp.ClientSession(timeout=timeout) as session:
        async with session.get(url) as resp:
            resp.raise_for_status()
            if not total_bytes:
                total_bytes = int(resp.headers.get("Content-Length", 0) or 0)
            downloaded = 0
            with open(path, "wb") as f:
                async for chunk in resp.content.iter_chunked(1024 * 1024):
                    if cancel_event.is_set():
                        raise TransferCancelled()
                    f.write(chunk)
                    downloaded += len(chunk)
                    if on_progress:
                        await on_progress(downloaded, total_bytes)


# ===== API CALL =====
def _parse_size_string_to_mb(size_str: str) -> float:
    m = re.match(r'\s*([\d.]+)\s*([KMGT]?B)', size_str or "", re.I)
    if not m:
        return 0.0
    val = float(m.group(1))
    unit = m.group(2).upper()
    mult = {"B": 1 / 1024 / 1024, "KB": 1 / 1024, "MB": 1, "GB": 1024, "TB": 1024 * 1024}.get(unit, 1)
    return round(val * mult, 2)


def _normalize_diskwala_filename(data: dict) -> str:
    name = (data.get("name") or "file").strip()
    ext = (data.get("extension") or "bin").strip().lstrip(".")
    if ext and not name.lower().endswith(f".{ext.lower()}"):
        return f"{name}.{ext}"
    return name or f"file.{ext}"


async def fetch_diskwala_link(url: str) -> tuple[dict | None, str]:
    if not DISKWALA_API_KEY:
        return None, "DiskWala API key is not configured."

    try:
        timeout = aiohttp.ClientTimeout(total=30)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.get(
                f"{DISKWALA_API_BASE}/",
                params={"url": url, "key": DISKWALA_API_KEY},
            ) as resp:
                if resp.status != 200:
                    _record_api_result("diskwala", False, f"HTTP {resp.status}")
                    return None, f"API error HTTP {resp.status}"
                data = await resp.json(content_type=None)
    except Exception as e:
        _record_api_result("diskwala", False, f"{type(e).__name__}: {e}")
        return None, "Failed to fetch data."

    if not isinstance(data, dict):
        _record_api_result("diskwala", False, "invalid response")
        return None, "Failed to fetch data."

    direct_url = (data.get("direct_url") or "").strip()
    if not direct_url:
        api_msg = data.get("message") or data.get("error") or "No direct url in response."
        _record_api_result("diskwala", False, str(api_msg))
        return None, str(api_msg)

    size_bytes = int(data.get("size") or 0)
    full_name = _normalize_diskwala_filename(data)
    thumbnail = (data.get("thumbnail") or "").strip()
    media_type = (data.get("type") or "").lower()
    stream = direct_url if media_type.startswith("video") else ""

    _record_api_result("diskwala", True)
    return {
        "name": full_name,
        "size_mb": round(size_bytes / 1024 / 1024, 2),
        "link": direct_url,
        "stream": stream,
        "thumbnail": thumbnail,
        "source": "diskwala",
    }, ""


# ===== DOWNLOAD =====
async def _run_get_file_transfer(
    client: Client,
    *,
    chat_id: int,
    progress_msg_id: int,
    job_id: str,
    link: str,
    name: str,
    size_mb: float,
) -> None:
    cancel_event = _file_transfer_jobs[job_id]["cancel"]
    cancel_markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("⏹ Cancel", callback_data=f"gfcancel:{job_id}")]
    ])
    started = time.monotonic()
    last_edit = 0.0
    last_bytes = 0
    last_tick = started
    current = 0
    total = int(size_mb * 1024 * 1024) if size_mb > 0 else 0
    phase = "Downloading"

    async def _refresh(force: bool = False, **extra):
        nonlocal last_edit, last_bytes, last_tick, current, total, phase
        now = time.monotonic()
        dt = max(now - last_tick, 0.001)
        speed = max(0, current - last_bytes) / dt if not extra.get("finished") else 0
        if not force and (now - last_edit) < 1.5 and not extra.get("finished"):
            last_bytes = current
            last_tick = now
            return
        text = _transfer_progress_text(
            name=name,
            size_mb=size_mb,
            phase=phase,
            current=current,
            total=total,
            speed_bps=speed,
            elapsed=now - started,
            **extra,
        )
        markup = None if extra.get("finished") or extra.get("cancelled") or extra.get("error") else cancel_markup
        try:
            await client.edit_message_text(chat_id, progress_msg_id, text, reply_markup=markup)
        except MessageNotModified:
            pass
        except Exception:
            pass
        last_edit = now
        last_bytes = current
        last_tick = now

    async def _on_download_progress(done: int, file_total: int):
        nonlocal current, total
        current = done
        if file_total > 0:
            total = file_total
        await _refresh()

    os.makedirs("downloads", exist_ok=True)
    safe_name = re.sub(r'[<>:"/\\|?*]', "_", name) or "file.bin"
    path = f"downloads/{job_id}_{safe_name}"

    try:
        await _refresh(force=True)
        await download_file_with_progress(
            link,
            path,
            cancel_event=cancel_event,
            total_bytes=total,
            on_progress=_on_download_progress,
        )
        if cancel_event.is_set():
            raise TransferCancelled()

        file_size = os.path.getsize(path)
        phase = "Uploading"
        current = 0
        total = file_size
        await _refresh(force=True)

        async def _on_upload_progress(sent: int, file_total: int):
            nonlocal current, total
            if cancel_event.is_set():
                raise TransferCancelled()
            current = sent
            if file_total > 0:
                total = file_total
            await _refresh()

        sent = await client.send_document(
            chat_id,
            path,
            caption=_file_caption(name, size_mb),
            progress=_on_upload_progress,
        )
        _schedule_delete_message(client, sent.chat.id, sent.id)
        await _refresh(force=True, finished=True)
    except TransferCancelled:
        await _refresh(force=True, cancelled=True, finished=True)
    except Exception as e:
        await _refresh(force=True, error="Transfer failed. Please try again.", finished=True)
        await report_error(client, "get_file_transfer", e, extra={"user_id": _file_transfer_jobs.get(job_id, {}).get("user_id")})
    finally:
        _file_transfer_jobs.pop(job_id, None)
        if os.path.exists(path):
            try:
                os.remove(path)
            except Exception:
                pass


async def send_premium_menu(message, user_id: int):
    if not _is_premium_enabled():
        return await message.reply(
            "Premium is not configured yet.\n\n"
            "Admin must set MongoDB env vars on server."
        )

    premium_until = await _get_premium_until(user_id)
    if premium_until and premium_until > _utc_now():
        status_text = f"✅ Active till: {premium_until.strftime('%Y-%m-%d %H:%M UTC')}"
    else:
        status_text = "❌ Not active"

    rows = []
    for key, plan in PREMIUM_PLANS.items():
        if plan.get("is_addon"):
            continue
            # TEMP: hidden to push weekly/monthly upgrades — restore by uncommenting (search "TEMP: hide-day-plan")
            if key == "day":
                continue

        addon_tag = " (Add-on)" if plan.get("is_addon") else ""
        rows.append([InlineKeyboardButton(
            f"💳 {plan['label']}{addon_tag} - ₹{plan['amount_inr']} / ⭐️{plan.get('stars', '-')}",
            callback_data=f"buyplan:{key}"
        )])

    premium_text = (
        "💎 Premium & Add-on Plans\n"
        f"- Daily limit: {PREMIUM_DAILY_DOWNLOADS} downloads/day\n"
        "- No ad unlock steps during active period\n\n"
        f"Your status: {status_text}"
    )

    await message.reply(
        premium_text,
        reply_markup=InlineKeyboardMarkup(rows),
    )


async def send_quota_topup_menu(message, user_id: int, daily_limit: int):
    plan = PREMIUM_PLANS.get("quota50")
    if not plan:
        return await message.reply("Top-up plan is unavailable right now.")
    text = (
        f"⚠️ Daily limit reached ({daily_limit}/day).\n\n"
        f"Need more today?\n"
        f"Buy {plan['label']} for ₹{plan['amount_inr']} / ⭐️{plan.get('stars', '-')}"
    )
    await message.reply(
        text,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("➕ Buy Quota Top-up", callback_data="buyplan:quota50")]
        ]),
    )


# ===== START HANDLER =====
@app.on_message(filters.command("start"))
async def start(client, message):
    user_id = message.from_user.id
    await _upsert_user_profile(message.from_user, client.bot_key)
    args = message.text.split(" ")

    text = message.caption if message.caption else message.text
    if _is_livegram_noise(text or ""):
        try:
            await message.delete()
        except Exception:
            pass
        return

    # 🔓 Unlock flow
    if len(args) > 1:
        token = args[1]
        if token == "premium":
            return await send_premium_menu(message, user_id)

        if not QUOTA_ENABLED:
            return await send_premium_required_once(client, message, user_id)

        data = tokens.get(token)

        if data and (not data["used"]) and data["user_id"] == user_id and data.get("expires_at", 0) > _now_ts():
            data["used"] = True

            lock = _get_user_lock(user_id)
            async with lock:
                state = await _get_quota_state(user_id, daily_limit=LIMIT_FREE_REQUESTS)
                new_remaining = int(state.get("remaining", 0)) + LIMIT_FREE_REQUESTS
                if users_col is None:
                    state["remaining"] = new_remaining
                    user_data[user_id] = state
                else:
                    await users_col.update_one(
                        {"user_id": int(user_id)},
                        {"$set": {"quota.remaining": new_remaining, "updated_at": _utc_now()}},
                        upsert=True,
                    )

            return await message.reply(
                f"Congrants ✅ Ad Unlocked ! \n\nYou got more +{LIMIT_FREE_REQUESTS} downloads Limit")

    await message.reply(
        "Welcome to DiskWala Downloader from @BotsXP |\n\n"
        "Send DiskWala links to get started.\n\n"
        f"Supported domains:\n{_supported_diskwala_domains_text()}"
    )


@app.on_message(filters.command("premium"))
async def premium_cmd(client, message):
    user_id = message.from_user.id
    await _upsert_user_profile(message.from_user, client.bot_key)
    if not await _ensure_joined(client, message):
        return
    await send_premium_menu(message, user_id)


@app.on_message(filters.command("myplan"))
async def myplan_cmd(client, message):
    user_id = message.from_user.id
    await _upsert_user_profile(message.from_user, client.bot_key)
    if not await _ensure_joined(client, message):
        return
    text, markup = await _get_plan_text_and_markup(user_id)
    await message.reply(text, reply_markup=markup)


@app.on_message(filters.command("status"))
async def status_cmd(client, message):
    user_id = message.from_user.id
    await _upsert_user_profile(message.from_user, client.bot_key)
    if int(user_id) not in ADMIN_USER_IDS:
        return await message.reply("❌ You are not allowed to use this command.")
    await message.reply(await _status_text(client.bot_key))


@app.on_message(filters.command("shortlink_on"))
async def shortlink_on_cmd(client, message):
    global QUOTA_ENABLED
    user_id = message.from_user.id
    if int(user_id) not in ADMIN_USER_IDS:
        return await message.reply("❌ You are not allowed to use this command.")
    QUOTA_ENABLED = True
    return await message.reply("OK. Shortlink unlock ENABLED. After free quota, users can watch an ad to get more downloads.")
    await message.reply("✅ Quota mechanism ENABLED. Free users now go through the shortlink/ad-unlock flow.")


@app.on_message(filters.command("shortlink_off"))
async def shortlink_off_cmd(client, message):
    global QUOTA_ENABLED
    user_id = message.from_user.id
    if int(user_id) not in ADMIN_USER_IDS:
        return await message.reply("❌ You are not allowed to use this command.")
    QUOTA_ENABLED = False
    return await message.reply("OK. Shortlink unlock DISABLED. Free users still get 3 downloads, then must buy premium.")
    await message.reply("✅ Quota mechanism DISABLED. All users get unlimited downloads (no credit checks).")


@app.on_message(filters.command("freemode_on"))
async def freemode_on_cmd(client, message):
    global FREE_MODE_ENABLED
    user_id = message.from_user.id
    if int(user_id) not in ADMIN_USER_IDS:
        return await message.reply("❌ You are not allowed to use this command.")
    FREE_MODE_ENABLED = True
    await message.reply("✅ Free mode ENABLED. Bot is free for all users until turned off.")


@app.on_message(filters.command("freemode_off"))
async def freemode_off_cmd(client, message):
    global FREE_MODE_ENABLED
    user_id = message.from_user.id
    if int(user_id) not in ADMIN_USER_IDS:
        return await message.reply("❌ You are not allowed to use this command.")
    FREE_MODE_ENABLED = False
    await message.reply("✅ Free mode DISABLED. Normal quota/premium rules apply again.")


@app.on_message(filters.command("sendfile_on"))
async def sendfile_on_cmd(client, message):
    global SENDFILE_ENABLED
    user_id = message.from_user.id
    if int(user_id) not in ADMIN_USER_IDS:
        return await message.reply("❌ You are not allowed to use this command.")
    SENDFILE_ENABLED = True
    await message.reply("✅ Get File (Premium) ENABLED. Premium users can download files again.")


@app.on_message(filters.command("sendfile_off"))
async def sendfile_off_cmd(client, message):
    global SENDFILE_ENABLED
    user_id = message.from_user.id
    if int(user_id) not in ADMIN_USER_IDS:
        return await message.reply("❌ You are not allowed to use this command.")
    SENDFILE_ENABLED = False
    await message.reply(
        "✅ Get File (Premium) DISABLED. The button stays visible, but users see a temporary-closed popup."
    )


@app.on_message(filters.command("broadcast"))
async def broadcast_cmd(client, message):
    user_id = message.from_user.id
    await _upsert_user_profile(message.from_user, client.bot_key)
    if int(user_id) not in ADMIN_USER_IDS:
        return await message.reply("❌ You are not allowed to use this command.")

    users = await _iter_all_user_ids(client.bot_key)
    if not users:
        return await message.reply("No users found to broadcast.")

    command_text = (message.text or "").strip()
    payload_text = ""
    if " " in command_text:
        payload_text = command_text.split(" ", 1)[1].strip()

    src = message.reply_to_message
    if src is None and not payload_text:
        return await message.reply(
            "Usage:\n"
            "1) `/broadcast your text`\n"
            "2) Reply to any media/text and send `/broadcast`\n"
            "3) Reply to media and send `/broadcast your new caption`"
        )

    job_id = f"{int(_now_ts()):x}"[-8:]
    cancel_event = asyncio.Event()
    _broadcast_jobs[job_id] = {"cancel": cancel_event, "admin_id": int(user_id)}

    total = len(users)
    sent_count = 0
    fail_count = 0
    removed_count = 0
    done = 0
    started = time.monotonic()
    last_edit = 0.0
    src_id = src.id if src is not None else None

    cancel_markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("⏹ Cancel broadcast", callback_data=f"bcancel:{job_id}")]
    ])
    status = await message.reply(
        _broadcast_progress_text(
            total=total,
            done=0,
            sent=0,
            failed=0,
            removed=0,
            elapsed=0.0,
        ),
        reply_markup=cancel_markup,
    )

    cancelled = False
    for target_id in users:
        if cancel_event.is_set():
            cancelled = True
            break

        outcome = await _broadcast_send_one(
            client,
            target_id=int(target_id),
            admin_chat_id=message.chat.id,
            src_message_id=src_id,
            payload_text=payload_text,
            bot_key=client.bot_key,
        )
        done += 1
        if outcome == "sent":
            sent_count += 1
        elif outcome in ("blocked", "removed"):
            removed_count += 1
        else:
            fail_count += 1

        now = time.monotonic()
        elapsed = now - started
        if now - last_edit >= 2.0 or done == total:
            last_edit = now
            await _broadcast_edit_status(
                client,
                status.chat.id,
                status.id,
                _broadcast_progress_text(
                    total=total,
                    done=done,
                    sent=sent_count,
                    failed=fail_count,
                    removed=removed_count,
                    elapsed=elapsed,
                    cancelled=cancelled,
                ),
                markup=cancel_markup if not cancelled and done < total else None,
            )

    elapsed = time.monotonic() - started
    _broadcast_jobs.pop(job_id, None)
    await _broadcast_edit_status(
        client,
        status.chat.id,
        status.id,
        _broadcast_progress_text(
            total=total,
            done=done,
            sent=sent_count,
            failed=fail_count,
            removed=removed_count,
            elapsed=elapsed,
            cancelled=cancelled,
            finished=True,
        ),
        markup=None,
    )


# ===== MAIN HANDLER =====
@app.on_message(filters.command("usage"))
async def usage_cmd(client, message):
    user_id = message.from_user.id
    await _upsert_user_profile(message.from_user, client.bot_key)
    if int(user_id) not in ADMIN_USER_IDS:
        return await message.reply("❌ You are not allowed to use this command.")
    if not DISKWALA_API_KEY:
        return await message.reply("DISKWALA_API_KEY is not configured.")

    status = await message.reply("Fetching usage info...")
    try:
        timeout = aiohttp.ClientTimeout(total=30)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.get(
                f"{DISKWALA_API_BASE}/usage",
                params={"key": DISKWALA_API_KEY},
            ) as resp:
                resp.raise_for_status()
                data = await resp.json(content_type=None)
    except Exception as e:
        return await status.edit(f"Failed to fetch usage: {e}")

    await status.edit(_format_api_usage(data))


def _human_size(n):
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n:.2f}{unit}"
        n /= 1024
    return f"{n:.2f}TB"


def _format_usage_value(key, value):
    key_lower = key.lower()
    if any(part in key_lower for part in ("key", "token", "secret", "password")):
        return "***"
    if isinstance(value, (int, float)) and any(
        part in key_lower for part in ("size", "bytes", "bandwidth", "traffic", "storage")
    ):
        return _human_size(value)
    return str(value)


def _format_api_usage(data: dict) -> str:
    if not data:
        return "Usage info is empty."

    lines = ["Usage:"]

    def add_items(items, prefix=""):
        for key, value in items.items():
            label = f"{prefix}{str(key).replace('_', ' ').title()}"
            if isinstance(value, dict):
                lines.append(f"{label}:")
                add_items(value, prefix="  ")
            elif isinstance(value, list):
                lines.append(f"{label}: {', '.join(map(str, value)) if value else 'None'}")
            else:
                lines.append(f"{label}: {_format_usage_value(str(key), value)}")

    add_items(data)
    return "\n".join(lines)


@app.on_message(filters.private & ~filters.command([
    "start", "premium", "myplan", "status", "usage", "broadcast",
    "shortlink_on", "shortlink_off", "freemode_on", "freemode_off",
    "sendfile_on", "sendfile_off",
]))
async def diskwala(client, message):
    user_id = message.from_user.id
    await _upsert_user_profile(message.from_user, client.bot_key)

    # Ignore queued old updates delivered after restart/deploy
    # to avoid mass "invalid link" replies to historical chats.
    msg_dt = getattr(message, "date", None)
    if isinstance(msg_dt, datetime):
        if msg_dt.tzinfo is None:
            msg_dt = msg_dt.replace(tzinfo=timezone.utc)
        if msg_dt < (BOT_BOOT_TIME_UTC - timedelta(seconds=10)):
            return

    text = message.caption if message.caption else message.text
    if _is_livegram_noise(text or ""):
        try:
            await message.delete()
        except Exception:
            pass
        return

    # Ignore plain texts without URL-like content to avoid noisy replies.
    # This keeps bot responses focused on actual link attempts only.
    if "http://" not in (text or "") and "https://" not in (text or ""):
        return

    if not await _ensure_joined(client, message):
        return

    try:
        urls = extract_urls(message, limit=MAX_LINKS_PER_MESSAGE)
        diskwala_urls = [u for u in urls if _looks_like_diskwala(u)]

        if not diskwala_urls:
            await _reply_invalid_link_once(client, message, user_id)
            return

        for idx, url in enumerate(diskwala_urls[:MAX_LINKS_PER_MESSAGE], start=1):
            skip_quota = FREE_MODE_ENABLED
            if skip_quota:
                ok_credit, is_premium, daily_limit = True, True, 0
            else:
                ok_credit, is_premium, daily_limit = await reserve_credit(user_id)
            if not ok_credit:
                if is_premium:
                    await message.reply(
                        f"💎 Premium daily limit reached ({daily_limit}/day). Please try again after UTC midnight."
                    )
                    await send_quota_topup_menu(message, user_id, daily_limit=daily_limit)
                else:
                    if QUOTA_ENABLED:
                        await send_unlock_once(client, message, user_id)
                    else:
                        await send_premium_required_once(client, message, user_id)
                return

            msg = await message.reply(f"Fetching ({idx}/{len(diskwala_urls[:MAX_LINKS_PER_MESSAGE])})...")
            result, err_msg = await fetch_diskwala_link(url)

            if not result:
                await msg.edit(
                    f"Failed ❌\n\n{err_msg}",
                    reply_markup=_support_markup(),
                )
                # refund reserved credit because request didn't succeed
                if not skip_quota:
                    await refund_reserved_credit(user_id, daily_limit=daily_limit, n=1)
                continue  # do NOT consume credits for invalid links

            name = result["name"]
            size_mb = result["size_mb"]
            link = result["link"]
            stream = result["stream"]
            thumbnail = result["thumbnail"]

            ftoken = create_file_token(link, name, size_mb, stream, user_id)
            caption = _file_options_caption(name, size_mb, has_stream=bool(stream))
            markup = _build_file_options_markup(
                ftoken,
                stream=stream,
                name=name,
                size_mb=size_mb,
                download_url=link,
            )

            if not markup:
                await msg.edit(
                    f"📁 {name}\n📦 {size_mb} MB\n\n⚠️ No delivery options available.",
                    reply_markup=_support_markup(),
                )
                continue

            await _send_file_options_message(
                client,
                message,
                msg,
                caption=caption,
                markup=markup,
                thumbnail=thumbnail,
            )

    except Exception as e:
        await report_error(client, "diskwala_handler", e, extra={"user_id": user_id})
        try:
            await message.reply(
                "Something went wrong. Please try again later.",
                reply_markup=_support_markup(),
            )
        except Exception:
            pass


@app.on_callback_query(filters.regex(r"^gfile:([a-zA-Z0-9]{16})$"))
async def get_file_cb(client, callback_query):
    user_id = callback_query.from_user.id
    token = callback_query.data.split(":", 1)[1]
    data = file_tokens.get(token)
    if not data or data.get("expires_at", 0) <= _now_ts():
        return await callback_query.answer("Session expired. Send the link again.", show_alert=True)
    if int(data.get("user_id", 0)) != user_id:
        return await callback_query.answer("Not your request.", show_alert=True)

    if not await _has_premium_access(user_id):
        return await callback_query.answer(
            "Get File is a Premium feature. Use /premium to upgrade.",
            show_alert=True,
        )
    if not SENDFILE_ENABLED:
        return await callback_query.answer(
            "Admin has temporarily closed Get File. Please try again later.",
            show_alert=True,
        )

    link = (data.get("link") or "").strip()
    name = data.get("name") or "file"
    size_mb = float(data.get("size_mb") or 0)

    if size_mb > TELEGRAM_MAX_UPLOAD_MB:
        return await callback_query.answer(
            f"File exceeds Telegram limit ({TELEGRAM_MAX_UPLOAD_MB:.0f} MB). Use Watch Online.",
            show_alert=True,
        )
    if not _is_valid_http_url(link):
        return await callback_query.answer("File URL unavailable.", show_alert=True)

    await callback_query.answer("Starting premium file transfer…")

    job_id = "".join(random.choices("0123456789abcdef", k=8))
    _file_transfer_jobs[job_id] = {"cancel": asyncio.Event(), "user_id": user_id}
    est_total = int(size_mb * 1024 * 1024) if size_mb > 0 else 0
    est_eta_note = ""
    if size_mb > 0:
        est_eta_note = f"\nEstimated size: {size_mb} MB — speed and ETA update live below."

    progress_msg = await callback_query.message.reply(
        _transfer_progress_text(
            name=name,
            size_mb=size_mb,
            phase="Preparing",
            current=0,
            total=est_total,
            speed_bps=0,
            elapsed=0,
        ) + est_eta_note,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("⏹ Cancel", callback_data=f"gfcancel:{job_id}")]
        ]),
    )

    asyncio.create_task(_run_get_file_transfer(
        client,
        chat_id=progress_msg.chat.id,
        progress_msg_id=progress_msg.id,
        job_id=job_id,
        link=link,
        name=name,
        size_mb=size_mb,
    ))


@app.on_callback_query(filters.regex(r"^gfcancel:([a-f0-9]{8})$"))
async def get_file_cancel_cb(client, callback_query):
    user_id = callback_query.from_user.id
    job_id = callback_query.data.split(":", 1)[1]
    job = _file_transfer_jobs.get(job_id)
    if not job:
        return await callback_query.answer("Nothing to cancel.", show_alert=False)
    if int(job.get("user_id", 0)) != user_id:
        return await callback_query.answer("Not allowed.", show_alert=True)
    job["cancel"].set()
    await callback_query.answer("Cancelling…", show_alert=False)


@app.on_callback_query(filters.regex(r"^bcancel:([a-f0-9]{8})$"))
async def broadcast_cancel_cb(client, callback_query):
    if int(callback_query.from_user.id) not in ADMIN_USER_IDS:
        return await callback_query.answer("❌ Not allowed.", show_alert=True)
    job_id = callback_query.data.split(":", 1)[1]
    job = _broadcast_jobs.get(job_id)
    if not job:
        return await callback_query.answer("This broadcast is already finished.", show_alert=True)
    job["cancel"].set()
    await callback_query.answer("Cancelling broadcast…", show_alert=False)


@app.on_callback_query(filters.regex(r"^check_join$"))
async def check_join_cb(client, callback_query):
    user_id = callback_query.from_user.id
    chat_ref = _force_sub_chat_ref()
    if chat_ref is None:
        await callback_query.answer("Join link is configured as invite; skipping verification.", show_alert=True)
        return
    try:
        m = await client.get_chat_member(chat_ref, user_id)
        is_joined = m.status not in (ChatMemberStatus.LEFT, ChatMemberStatus.BANNED)
    except ChatAdminRequired:
        await callback_query.answer(
            f"Bot is not admin in {FORCE_SUB_CHANNEL}. Ask admin to add bot as admin, then try again.",
            show_alert=True,
        )
        return
    except Exception:
        is_joined = False

    if is_joined:
        try:
            await callback_query.message.edit_text("✅ Verified! Now send your DiskWala link.")
        except ChatWriteForbidden:
            pass
        await callback_query.answer("Verified ✅", show_alert=False)
        return

    await callback_query.answer("Not joined yet. Please join the channel first.", show_alert=True)


@app.on_callback_query(filters.regex(r"^buyplan:([a-zA-Z0-9_]+)$"))
async def buy_plan_cb(client, callback_query):
    user_id = callback_query.from_user.id
    plan_key = callback_query.data.split(":", 1)[1]
    plan = PREMIUM_PLANS.get(plan_key)
    if not plan:
        return await callback_query.answer("Invalid plan selected.", show_alert=True)
    await callback_query.answer("Choose payment method", show_alert=False)
    await callback_query.message.reply(
        (
            f"💳 {plan['label']}\n"
            f"Amount: ₹{plan['amount_inr']} or ⭐️{plan.get('stars', '-')}\n\n"
            "Select payment method:"
        ),
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("1) UPI QR", callback_data=f"paymethod:{plan_key}:upiqr")],
            [InlineKeyboardButton("2) Cards / Wallet", callback_data=f"paymethod:{plan_key}:cards")],
            [InlineKeyboardButton("3) Telegram Stars", callback_data=f"paymethod:{plan_key}:stars")],
        ]),
    )


@app.on_callback_query(filters.regex(r"^paymethod:([a-zA-Z0-9_]+):(upiqr|cards|stars)$"))
async def pay_method_cb(client, callback_query):
    user_id = callback_query.from_user.id
    _, plan_key, method = callback_query.data.split(":")
    plan = PREMIUM_PLANS.get(plan_key)
    if not plan:
        return await callback_query.answer("Invalid plan selected.", show_alert=True)
    progress_msg = None
    try:
        if method in ("upiqr", "cards") and not _is_razorpay_enabled():
            return await callback_query.answer("UPI/Card payment unavailable right now.", show_alert=True)
        if method == "stars":
            stars_amount = int(plan.get("stars") or 0)
            if stars_amount <= 0:
                return await callback_query.answer("Stars payment unavailable for this plan.", show_alert=True)
            await _send_stars_invoice(
                client,
                callback_query.message.chat.id,
                user_id,
                plan_key,
                plan,
            )
            await callback_query.message.reply(
                "⭐ After successful Stars payment, activation is automatic.\n"
                "If it takes more than 20 seconds, send /myplan to refresh status."
            )
            return await callback_query.answer("Stars invoice sent ✅", show_alert=False)

        await callback_query.answer("Creating payment...", show_alert=False)
        progress_msg = await callback_query.message.reply(
            "⏳ Please wait around 10 seconds.\nPreparing your selected payment method..."
        )
        await _close_user_active_payment_sessions(user_id)
        pay_ref = ''.join(random.choices(string.ascii_letters + string.digits, k=18))
        payment_link_id = ""
        short_url = ""
        qr_image_url = ""
        qr_code_id = ""

        if method == "cards":
            link_data = await _create_razorpay_payment_link(user_id, plan_key, pay_ref)
            payment_link_id = link_data.get("id", "")
            short_url = link_data.get("short_url", "")
            if not short_url:
                raise RuntimeError("Missing payment link URL from Razorpay")
        elif method == "upiqr":
            qr_data = await _create_razorpay_upi_qr(user_id, plan_key, pay_ref)
            qr_image_url = qr_data.get("image_url", "")
            qr_code_id = qr_data.get("id", "")
            if not qr_image_url:
                raise RuntimeError("Missing QR image URL from Razorpay")
        else:
            return await callback_query.answer("Invalid payment method.", show_alert=True)

        if payments_col is not None:
            await payments_col.update_one(
                {"pay_ref": pay_ref},
                {"$set": {
                    "pay_ref": pay_ref,
                    "payment_link_id": payment_link_id,
                    "qr_code_id": qr_code_id,
                    "user_id": int(user_id),
                    "plan_key": plan_key,
                    "status": "created",
                    "short_url": short_url,
                    "created_at": _utc_now(),
                    "expires_at": _now_ts() + PAYMENT_SESSION_TTL_SECONDS,
                    "source": f"create:{method}",
                    "payment_method": method,
                }},
                upsert=True,
            )

        payment_post = None
        if method == "upiqr":
            qr_photo = await _download_qr_image_for_upload(qr_image_url, pay_ref)
            payment_post = await callback_query.message.reply_photo(
                photo=qr_photo,
                caption=(
                    f"💳 Plan: {plan['label']} - ₹{plan['amount_inr']}\n\n"
                    f"Reference ID: {pay_ref}\n\n"
                    "<b>➡️ Pay using UPI QR (Recommended)</b>\n\n"
                    "<u>STEPS to Pay using QR</u>\n"
                    "1) Save above QR & Open any UPI app (GPay/PhonePe/Paytm/BHIM).\n"
                    "2) Upload and Scan this QR directly.\n"
                    f"3) Pay ₹{plan['amount_inr']} only.\n"
                    "4) Return here and tap ✅ I Have Paid.\n\n"
                    "<b>Tutorial: <a href='https://t.me/howdisk/4'>Click Here</a></b>\n\n"
                    "<b>This payment session is valid for 15 minutes.\n</b>"
                ),
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("✅ I Have Paid", callback_data=f"checkpay:{pay_ref}")],
                    [InlineKeyboardButton("🎥 Tutorial", url="https://t.me/howdisk/4")],
                ]),
            )
        elif method == "cards":
            payment_post = await callback_query.message.reply(
                f"💳 Plan: {plan['label']} - ₹{plan['amount_inr']}\n\n"
                "Use the payment link below to pay via Card/UPI apps/Wallet.\n"
                "After payment, tap ✅ I Have Paid.",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔐 Payment Link", url=short_url)],
                    [InlineKeyboardButton("✅ I Have Paid", callback_data=f"checkpay:{pay_ref}")],
                    [InlineKeyboardButton("🎥 Tutorial", url="https://t.me/howdisk/5")],
                ]),
                disable_web_page_preview=True,
            )
        if payment_post:
            _schedule_delete_payment_post_in(
                client,
                payment_post.chat.id,
                payment_post.id,
                PAYMENT_SESSION_TTL_SECONDS
            )
        if progress_msg:
            try:
                await progress_msg.delete()
            except Exception:
                pass
    except Exception as e:
        if progress_msg:
            try:
                await progress_msg.delete()
            except Exception:
                pass
        await report_error(client, "pay_method_cb", e, extra={"user_id": user_id, "plan_key": plan_key, "method": method})
        await callback_query.message.reply("Failed to create payment link. Please try again in a moment.")


@app.on_callback_query(filters.regex(r"^checkpay:"))
async def check_pay_cb(client, callback_query):
    user_id = callback_query.from_user.id
    pay_ref = callback_query.data.split(":", 1)[1].strip()
    if not pay_ref:
        return await callback_query.answer("Invalid payment reference.", show_alert=True)
    try:
        await callback_query.answer("Checking payment status...", show_alert=False)
        if payments_col is None:
            return await callback_query.message.reply("Payment check needs database enabled. Please try later.")

        attempt = await payments_col.find_one(
            {"pay_ref": pay_ref},
            {"payment_link_id": 1, "qr_code_id": 1, "user_id": 1, "plan_key": 1, "expires_at": 1}
        )
        if not attempt:
            return await callback_query.message.reply(
                "❌ Payment session not found. Please generate a new plan payment.")
        if int(attempt.get("user_id") or 0) != int(user_id):
            return await callback_query.message.reply("❌ This payment session belongs to another user.")

        expires_at = float(attempt.get("expires_at") or 0)
        if expires_at and _now_ts() > expires_at:
            await payments_col.update_one(
                {"pay_ref": pay_ref},
                {"$set": {"status": "expired", "updated_at": _utc_now()}},
            )
            await _close_payment_session(pay_ref)
            return await callback_query.message.reply(
                "⌛ Payment session expired (15 minutes).\n"
                "Please choose a plan again to generate a fresh payment.\n"
                "/premium"
            )

        payment_link_id = attempt.get("payment_link_id", "")
        qr_code_id = attempt.get("qr_code_id", "")
        plan_key = attempt.get("plan_key")
        plan = PREMIUM_PLANS.get(plan_key) if plan_key else None
        payment_id = ""
        status = ""
        if payment_link_id:
            data = await _get_razorpay_payment_link(payment_link_id)
            status = (data.get("status") or "").lower()
            payment_id = data.get("payment_id") or ""

        qr_paid = False
        if qr_code_id and plan:
            qr_data = await _get_razorpay_qr(qr_code_id)
            received = int(qr_data.get("payments_amount_received") or 0)
            payments_count = int(qr_data.get("payments_count") or 0)
            expected_amount = int(plan["amount_inr"]) * 100
            if received >= expected_amount or payments_count > 0:
                qr_paid = True
                if not payment_id:
                    payments = qr_data.get("payments") or []
                    if isinstance(payments, list) and payments:
                        first_payment = payments[0] or {}
                        payment_id = first_payment.get("id") or payment_id

        paid_via_webhook = await payments_col.find_one(
            {"pay_ref": pay_ref, "status": "paid"},
            {"payment_id": 1, "plan_key": 1}
        )

        if status != "paid" and not qr_paid and not paid_via_webhook:
            return await callback_query.message.reply(
                "❌ Payment not received yet.\n"
                "Please complete payment, wait 5-10 seconds, then tap ✅ I Have Paid again."
            )

        if paid_via_webhook and not payment_id:
            payment_id = paid_via_webhook.get("payment_id") or ""
            plan_key = paid_via_webhook.get("plan_key") or plan_key

        already_done = False
        if payment_id:
            existing = await payments_col.find_one({"payment_id": payment_id, "status": "paid"}, {"_id": 1})
            already_done = bool(existing)

        await payments_col.update_one(
            {"pay_ref": pay_ref},
            {"$set": {
                "pay_ref": pay_ref,
                "payment_link_id": payment_link_id,
                "payment_id": payment_id,
                "user_id": int(user_id),
                "plan_key": plan_key,
                "status": "paid",
                "paid_at": _utc_now(),
                "source": "manual_check",
            }},
            upsert=True,
        )

        if not already_done and plan_key in PREMIUM_PLANS:
            result_text = await _apply_purchase(user_id, plan_key, payment_id=payment_id)
            await _close_payment_session(pay_ref)
            await callback_query.message.reply(result_text)
            await _notify_purchase(client, user_id, plan_key, payment_id=payment_id, source="manual_check")
        else:
            await _close_payment_session(pay_ref)
            await callback_query.message.reply("✅ Payment already processed.")
    except Exception as e:
        await report_error(client, "check_pay_cb", e, extra={"user_id": user_id, "pay_ref": pay_ref})
        await callback_query.message.reply("❌ Could not verify payment right now. Please try again shortly.")


@app.on_callback_query(filters.regex(r"^cancelpay:"))
async def cancel_pay_cb(client, callback_query):
    user_id = callback_query.from_user.id
    pay_ref = callback_query.data.split(":", 1)[1].strip()
    if not pay_ref:
        return await callback_query.answer("Invalid payment reference.", show_alert=True)
    if payments_col is None:
        return await callback_query.message.reply("Payment cancel requires database enabled.")
    attempt = await payments_col.find_one({"pay_ref": pay_ref}, {"user_id": 1, "status": 1})
    if not attempt:
        return await callback_query.message.reply("❌ Payment session not found.")
    if int(attempt.get("user_id") or 0) != int(user_id):
        return await callback_query.message.reply("❌ This payment session belongs to another user.")
    if (attempt.get("status") or "").lower() == "paid":
        return await callback_query.message.reply("✅ This payment is already completed.")

    await _close_payment_session(pay_ref)
    await payments_col.update_one(
        {"pay_ref": pay_ref},
        {"$set": {"status": "cancelled", "updated_at": _utc_now()}},
    )
    await callback_query.answer("Payment session cancelled.", show_alert=False)
    await callback_query.message.reply("❌ Payment session cancelled.\nUse /premium to create a new payment.")


@app.on_raw_update()
async def stars_payment_raw(client, update, users, chats):
    try:
        raw_updates = []
        if hasattr(update, "updates") and isinstance(getattr(update, "updates", None), list):
            raw_updates.extend(update.updates)
        elif hasattr(update, "update"):
            raw_updates.append(update.update)
        else:
            raw_updates.append(update)

        for u in raw_updates:
            if isinstance(u, raw.types.UpdateBotPrecheckoutQuery):
                await client.invoke(
                    raw.functions.messages.SetBotPrecheckoutResults(
                        query_id=u.query_id,
                        success=True,
                    )
                )
                try:
                    pre_payload = (u.payload or b"").decode("utf-8", errors="ignore")
                    await _process_stars_payment(
                        client,
                        int(getattr(u, "user_id", 0) or 0),
                        pre_payload,
                        getattr(u, "currency", ""),
                        int(getattr(u, "total_amount", 0) or 0),
                        payment_id=f"precheckout_{int(u.query_id)}",
                    )
                except Exception as pre_err:
                    await report_error(client, "stars_precheckout_process", pre_err)
                continue

            msg = None
            if isinstance(u, (raw.types.UpdateNewMessage, raw.types.UpdateNewChannelMessage)):
                msg = u.message
            if not isinstance(msg, raw.types.MessageService):
                continue
            action = msg.action
            if isinstance(action, raw.types.MessageActionPaymentSentMe):
                user_id = _extract_user_id_from_service_message(msg)
                payload = action.payload.decode("utf-8", errors="ignore")
                payment_id = getattr(action.charge, "id", "") or getattr(action.charge, "provider_charge_id", "")
                await _process_stars_payment(
                    client,
                    user_id,
                    payload,
                    action.currency,
                    int(action.total_amount),
                    payment_id,
                )
            elif isinstance(action, raw.types.MessageActionPaymentSent):
                await _process_stars_payment_sent_fallback(client, msg, action)
    except Exception as e:
        await report_error(client, "stars_payment_raw", e)


@bot.get("/premium/checkout/<pay_token>")
async def premium_checkout(pay_token: str):
    if not _is_premium_enabled():
        return Response("Premium payment is not configured on server.", status=503)
    _cleanup_expired_tokens()
    data = payment_tokens.get(pay_token)
    if not data or data.get("expires_at", 0) <= _now_ts():
        return Response("Payment session expired. Open /premium again in bot.", status=410)

    user_id = int(data["user_id"])
    plan_key = data["plan_key"]
    if plan_key not in PREMIUM_PLANS:
        return Response("Invalid plan.", status=400)

    order = await _create_razorpay_order(user_id, plan_key, pay_token)
    order_id = order.get("id")
    if not order_id:
        return Response("Failed to create payment order.", status=500)

    if payments_col is not None:
        await payments_col.update_one(
            {"order_id": order_id},
            {"$set": {
                "order_id": order_id,
                "user_id": user_id,
                "plan_key": plan_key,
                "status": "created",
                "created_at": _utc_now(),
            }},
            upsert=True,
        )

    plan = PREMIUM_PLANS[plan_key]
    html = f"""<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>Premium Checkout</title>
  <script src="https://checkout.razorpay.com/v1/checkout.js"></script>
</head>
<body style="font-family: Arial, sans-serif; background:#0f1118; color:#fff; margin:0; padding:20px;">
  <h3>Premium Plan: {plan['label']}</h3>
  <p>Amount: ₹{plan['amount_inr']}</p>
  <button id="payBtn" style="padding:12px 18px;border-radius:8px;border:none;background:#4f7cff;color:#fff;">Pay Now</button>
  <p id="status" style="opacity:.9;"></p>
  <script>
    const statusEl = document.getElementById('status');
    const options = {{
      key: {RAZORPAY_KEY_ID!r},
      amount: {int(plan['amount_inr']) * 100},
      currency: "INR",
      name: "DiskWala DL Premium",
      description: "{plan['label']} plan",
      order_id: {order_id!r},
      prefill: {{}},
      theme: {{ color: "#4f7cff" }},
      handler: async function (resp) {{
        statusEl.textContent = "Verifying payment...";
        const r = await fetch("/premium/verify", {{
          method: "POST",
          headers: {{ "Content-Type": "application/json" }},
          body: JSON.stringify({{
            pay_token: {pay_token!r},
            razorpay_order_id: resp.razorpay_order_id,
            razorpay_payment_id: resp.razorpay_payment_id,
            razorpay_signature: resp.razorpay_signature
          }})
        }});
        const data = await r.json();
        statusEl.textContent = data.message || "Done";
      }}
    }};
    const rzp = new Razorpay(options);
    document.getElementById('payBtn').onclick = () => rzp.open();
  </script>
</body>
</html>"""
    return Response(html, mimetype="text/html")


@bot.post("/premium/verify")
async def premium_verify():
    if not _is_premium_enabled():
        return {"ok": False, "message": "Premium not configured"}, 503

    payload = await request.get_json(force=True)
    pay_token = (payload or {}).get("pay_token", "")
    order_id = (payload or {}).get("razorpay_order_id", "")
    payment_id = (payload or {}).get("razorpay_payment_id", "")
    signature = (payload or {}).get("razorpay_signature", "")

    _cleanup_expired_tokens()
    token_data = payment_tokens.get(pay_token)
    if not token_data:
        return {"ok": False, "message": "Payment session expired."}, 410
    if not _verify_razorpay_signature(order_id, payment_id, signature):
        return {"ok": False, "message": "Invalid payment signature."}, 400

    user_id = int(token_data["user_id"])
    plan_key = token_data["plan_key"]
    result_text = await _apply_purchase(user_id, plan_key, payment_id=payment_id)

    if payments_col is not None:
        await payments_col.update_one(
            {"order_id": order_id},
            {"$set": {
                "order_id": order_id,
                "payment_id": payment_id,
                "user_id": user_id,
                "plan_key": plan_key,
                "status": "paid",
                "paid_at": _utc_now(),
            }},
            upsert=True,
        )

    payment_tokens.pop(pay_token, None)
    try:
        await app.send_message(user_id, result_text)
    except Exception:
        pass
    await _notify_purchase(app, user_id, plan_key, payment_id=payment_id, source="checkout_verify")
    return {"ok": True, "message": result_text}


@bot.post("/razorpay/webhook")
async def razorpay_webhook():
    if not RAZORPAY_WEBHOOK_SECRET:
        return {"ok": False, "message": "Webhook secret missing"}, 503
    raw = await request.get_data()
    sig = request.headers.get("X-Razorpay-Signature", "")
    expected = hmac.new(RAZORPAY_WEBHOOK_SECRET.encode(), raw, hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected, sig):
        return {"ok": False, "message": "Bad signature"}, 400

    body = await request.get_json(force=True)
    event = (body or {}).get("event", "")
    payload = (body or {}).get("payload") or {}
    payment_entity = (payload.get("payment") or {}).get("entity") or {}
    payment_link_entity = (payload.get("payment_link") or {}).get("entity") or {}
    qr_entity = (payload.get("qr_code") or {}).get("entity") or {}

    if event not in ("payment.captured", "payment_link.paid"):
        return {"ok": True}

    notes = payment_entity.get("notes") or payment_link_entity.get("notes") or {}
    user_id = int(notes.get("user_id") or 0)
    plan_key = notes.get("plan_key")
    pay_ref = notes.get("pay_ref") or ""
    payment_id = payment_entity.get("id", "")
    order_id = payment_entity.get("order_id", "")
    payment_link_id = payment_link_entity.get("id", "")
    qr_code_id = qr_entity.get("id", "")
    payment_status = (payment_entity.get("status") or "").lower()
    payment_amount = int(payment_entity.get("amount") or 0)
    payment_link_status = (payment_link_entity.get("status") or "").lower()
    payment_link_paid = int(payment_link_entity.get("amount_paid") or 0)

    # For UPI-QR payments, notes may not always be present in webhook.
    # Resolve user/plan/session from our DB using qr_code_id or payment_link_id.
    if payments_col is not None and (not user_id or plan_key not in PREMIUM_PLANS):
        session_doc = None
        if qr_code_id:
            session_doc = await payments_col.find_one(
                {"qr_code_id": qr_code_id},
                {"user_id": 1, "plan_key": 1, "pay_ref": 1}
            )
        if not session_doc and payment_link_id:
            session_doc = await payments_col.find_one(
                {"payment_link_id": payment_link_id},
                {"user_id": 1, "plan_key": 1, "pay_ref": 1}
            )
        if session_doc:
            user_id = int(session_doc.get("user_id") or 0)
            plan_key = session_doc.get("plan_key")
            pay_ref = session_doc.get("pay_ref") or pay_ref

    # Hard guard: never activate without a known plan.
    if plan_key not in PREMIUM_PLANS:
        return {"ok": True}

    expected_amount = int(PREMIUM_PLANS[plan_key]["amount_inr"]) * 100

    # Ensure webhook event is genuinely paid/captured and amount matches expected plan.
    is_paid_event = False
    if event == "payment.captured":
        is_paid_event = payment_status == "captured" and payment_amount == expected_amount
    elif event == "payment_link.paid":
        is_paid_event = payment_link_status == "paid" and payment_link_paid >= expected_amount
    if not is_paid_event:
        return {"ok": True}

    # Resolve and validate session from DB to prevent accidental premium activation.
    session_doc = None
    if payments_col is not None:
        if pay_ref:
            session_doc = await payments_col.find_one({"pay_ref": pay_ref})
        if not session_doc and qr_code_id:
            session_doc = await payments_col.find_one({"qr_code_id": qr_code_id})
        if not session_doc and payment_link_id:
            session_doc = await payments_col.find_one({"payment_link_id": payment_link_id})

    if not session_doc:
        return {"ok": True}

    session_status = (session_doc.get("status") or "").lower()
    if session_status in ("paid", "expired", "cancelled", "cancelled_replaced"):
        return {"ok": True}

    # Always trust the stored session identity over webhook notes.
    user_id = int(session_doc.get("user_id") or 0)
    plan_key = session_doc.get("plan_key")
    pay_ref = session_doc.get("pay_ref") or pay_ref
    if not user_id or plan_key not in PREMIUM_PLANS:
        return {"ok": True}

    already_done = False
    if payments_col is not None and payment_id:
        existing = await payments_col.find_one({"payment_id": payment_id, "status": "paid"}, {"_id": 1})
        already_done = bool(existing)

    if user_id and plan_key in PREMIUM_PLANS and not already_done:
        result_text = await _apply_purchase(user_id, plan_key, payment_id=payment_id)
        if pay_ref:
            await _close_payment_session(pay_ref)
        if payments_col is not None:
            record_key = pay_ref or (f"qr:{qr_code_id}" if qr_code_id else "") or (
                        payment_id or f"plink:{payment_link_id}")
            await payments_col.update_one(
                {"pay_ref": record_key},
                {"$set": {
                    "pay_ref": pay_ref,
                    "order_id": order_id,
                    "payment_id": payment_id,
                    "payment_link_id": payment_link_id,
                    "qr_code_id": qr_code_id,
                    "user_id": user_id,
                    "plan_key": plan_key,
                    "status": "paid",
                    "paid_at": _utc_now(),
                    "source": f"webhook:{event}",
                }},
                upsert=True,
            )
        try:
            await app.send_message(user_id, result_text)
        except Exception:
            pass
        await _notify_purchase(app, user_id, plan_key, payment_id=payment_id, source=f"webhook:{event}")
    return {"ok": True}


def _should_this_bot_notify(client: Client, bots_map: dict | None) -> bool:
    """
    All 3 bots are deployed separately but share one DB, so every instance's
    reminder loop sees the same premium user doc. Only the bot the user most
    recently used should actually send the DM, or all 3 would message them.
    """
    if not bots_map:
        return True
    best_key, best_ts = None, None
    for k, v in bots_map.items():
        ts = (v or {}).get("last_seen_at")
        if isinstance(ts, datetime) and (best_ts is None or ts > best_ts):
            best_key, best_ts = k, ts
    if best_key is None:
        return True
    return best_key == getattr(client, "bot_key", None)


async def _send_premium_expiry_reminders(client: Client) -> None:
    if users_col is None:
        return
    now = _utc_now()
    cursor = users_col.find(
        {
            "premium_until": {"$type": "date"},
            "premium_tracking_enabled": True,
        },
        {"user_id": 1, "premium_until": 1, "premium_reminders": 1, "bots": 1}
    )
    async for doc in cursor:
        user_id = int(doc.get("user_id") or 0)
        premium_until = doc.get("premium_until")
        reminders = doc.get("premium_reminders") or {}
        if not user_id or not isinstance(premium_until, datetime):
            continue
        if not _should_this_bot_notify(client, doc.get("bots")):
            continue
        if premium_until.tzinfo is None:
            premium_until = premium_until.replace(tzinfo=timezone.utc)
        delta = premium_until - now
        set_fields = {}
        try:
            if delta.total_seconds() <= 0:
                if not reminders.get("expired_sent"):
                    # Avoid mass messaging historical expired users on first deploy.
                    # Notify only if expiry happened recently.
                    recently_expired = delta >= timedelta(hours=-max(1, PREMIUM_END_REMINDER_WINDOW_HOURS))
                    if recently_expired:
                        await client.send_message(
                            user_id,
                            "⚠️ Your premium plan has ended.\nUse /premium to renew and continue premium benefits."
                        )
                    set_fields["premium_reminders.expired_sent"] = True
            elif delta <= timedelta(hours=3):
                if not reminders.get("h3_sent"):
                    await client.send_message(
                        user_id,
                        "⏰ Reminder: Your premium plan will expire in about 3 hours."
                    )
                    set_fields["premium_reminders.h3_sent"] = True
            elif delta <= timedelta(days=1):
                if not reminders.get("d1_sent"):
                    await client.send_message(
                        user_id,
                        "📅 Reminder: Your premium plan will expire in about 1 day."
                    )
                    set_fields["premium_reminders.d1_sent"] = True
        except Exception:
            continue
        if set_fields:
            set_fields["updated_at"] = _utc_now()
            await users_col.update_one({"user_id": user_id}, {"$set": set_fields}, upsert=True)


async def _premium_reminder_loop(client: Client) -> None:
    while True:
        try:
            await _send_premium_expiry_reminders(client)
        except Exception as e:
            await report_error(client, "premium_reminder_loop", e)
        await asyncio.sleep(30 * 60)


@bot.get("/player/<token>")
async def player(token: str):
    data = stream_tokens.get(token)
    if not data or data.get("expires_at", 0) <= _now_ts():
        return Response("Stream link expired. Go back to the bot and generate again.", status=410)

    # We route the playback through our proxy to avoid CORS issues in Telegram WebView.
    proxied_m3u8 = f"/hls?u={quote_plus(data['url'])}"

    file_name = html.escape(data.get("name") or "video.mp4")
    size_mb = data.get("size_mb") or 0
    quality = html.escape(data.get("quality") or "")
    bot_username = html.escape(_current_bot_username() or "DiskWalaBot")
    loot_deals_url = "https://t.me/+SVbNsGtmvfUzYzNl"

    page = f"""<!doctype html>
<html>
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>{bot_username} | Video Downloader</title>
    <style>
      * {{ box-sizing: border-box; }}
      html, body {{ margin: 0; padding: 0; background: #05070d; color: #fff;
        font-family: system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif; }}
      .card {{ max-width: 480px; margin: 0 auto; background: #0b0f19; min-height: 100vh; }}
      .header {{ display: flex; align-items: center; gap: 12px; padding: 16px; border-bottom: 1px solid #1c2333; }}
      .header .icon {{ width: 40px; height: 40px; border-radius: 50%; background: #1471ef;
        display: flex; align-items: center; justify-content: center; flex-shrink: 0; }}
      .header .icon svg {{ width: 20px; height: 20px; stroke: #fff; fill: none; stroke-width: 2; }}
      .header .titles {{ flex: 1; min-width: 0; }}
      .header .titles .t {{ font-size: 15px; font-weight: 700; }}
      .header .titles .s {{ font-size: 12px; color: #8b93a7; margin-top: 2px; }}
      .player {{ position: relative; margin: 14px; border-radius: 14px; overflow: hidden; background: #000; }}
      video {{ width: 100%; display: block; aspect-ratio: 16/9; background: #000; }}
      .badge {{ position: absolute; top: 10px; font-size: 11px; font-weight: 700; padding: 4px 8px;
        border-radius: 6px; background: rgba(0,0,0,0.55); backdrop-filter: blur(4px); }}
      .badge.quality {{ left: 10px; display: flex; align-items: center; gap: 5px; }}
      .badge.quality .hd {{ background: #1471ef; padding: 1px 5px; border-radius: 4px; font-size: 9px; }}
      .badge.time {{ right: 10px; font-variant-numeric: tabular-nums; }}
      .center-play {{ position: absolute; top: 50%; left: 50%; transform: translate(-50%, -50%);
        width: 56px; height: 56px; border-radius: 50%; background: rgba(0,0,0,0.45);
        display: flex; align-items: center; justify-content: center; cursor: pointer; border: none; }}
      .center-play svg {{ width: 22px; height: 22px; fill: #fff; margin-left: 3px; }}
      .controls {{ position: absolute; left: 0; right: 0; bottom: 0; padding: 8px 10px 10px;
        background: linear-gradient(transparent, rgba(0,0,0,0.75)); }}
      .seek-row {{ display: flex; align-items: center; gap: 8px; font-size: 11px; color: #cfd5e3;
        font-variant-numeric: tabular-nums; }}
      .seek-row input[type=range] {{ flex: 1; height: 3px; accent-color: #1471ef; }}
      .btn-row {{ display: flex; align-items: center; gap: 16px; margin-top: 6px; }}
      .btn-row button {{ background: none; border: none; cursor: pointer; padding: 4px; }}
      .btn-row svg {{ width: 20px; height: 20px; stroke: #fff; fill: none; stroke-width: 2; }}
      .btn-row .spacer {{ flex: 1; }}
      .file-row {{ display: flex; align-items: center; gap: 10px; margin: 0 14px 14px; padding: 12px;
        background: #10162494; border-radius: 12px; border: 1px solid #1c2333; }}
      .file-row .f-icon {{ width: 36px; height: 36px; border-radius: 8px; background: #6c4fe0;
        display: flex; align-items: center; justify-content: center; flex-shrink: 0; }}
      .file-row .f-icon svg {{ width: 16px; height: 16px; fill: #fff; }}
      .file-row .f-meta {{ flex: 1; min-width: 0; }}
      .file-row .f-name {{ font-size: 13px; font-weight: 600; overflow: hidden; text-overflow: ellipsis;
        white-space: nowrap; }}
      .file-row .f-size {{ font-size: 12px; color: #8b93a7; margin-top: 2px; }}
      .hint {{ display: flex; gap: 10px; margin: 0 14px 14px; padding: 12px; border-radius: 12px;
        background: #10162494; border: 1px solid #1c2333; font-size: 12px; line-height: 1.5; color: #b9c0d1; }}
      .hint svg {{ width: 16px; height: 16px; stroke: #8b93a7; fill: none; stroke-width: 2; flex-shrink: 0; margin-top: 1px; }}
      .promo {{
        margin: 0 14px 14px;
        padding: 0;
        border-radius: 16px;
        overflow: hidden;
        position: relative;
        background: radial-gradient(120% 140% at 15% 0%, #3a1440 0%, #1a0f2e 35%, #0d1224 70%, #0b0f1e 100%);
        border: 1px solid rgba(255, 183, 77, 0.35);
        box-shadow: 0 8px 32px rgba(255, 90, 0, 0.18), inset 0 1px 0 rgba(255,255,255,0.06);
      }}
      .promo-top {{ padding: 16px 16px 12px; text-align: center; }}
      .promo-flash {{
        display: inline-flex; align-items: center; gap: 5px;
        background: linear-gradient(135deg, #ff6d00, #ff2d55);
        color: #fff; font-weight: 800; font-size: 10.5px; letter-spacing: 0.4px;
        padding: 4px 10px; border-radius: 999px; margin-bottom: 10px;
        box-shadow: 0 4px 14px rgba(255,45,85,0.35);
      }}
      .promo-title {{
        font-size: 20px; font-weight: 900; line-height: 1.2; letter-spacing: -0.3px;
        background: linear-gradient(135deg, #ffd580, #ff9900 55%, #ff5e3a);
        -webkit-background-clip: text; background-clip: text; color: transparent;
      }}
      .promo-sub {{ font-size: 12.5px; color: #d6dae8; margin-top: 8px; line-height: 1.5; }}
      .promo-sub b {{ color: #ffb74d; font-weight: 800; }}
      .promo-body {{ padding: 4px 16px 16px; }}
      .promo-pills {{
        display: flex; gap: 8px; margin-bottom: 14px;
      }}
      .promo-pill {{
        flex: 1; text-align: center; text-decoration: none;
        font-size: 11px; font-weight: 800; padding: 9px 6px; border-radius: 999px;
        color: #fff; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
      }}
      .promo-pill.loot {{ background: linear-gradient(135deg, #ff6d00, #ff9100); box-shadow: 0 4px 12px rgba(255,109,0,0.3); }}
      .promo-pill.error {{ background: linear-gradient(135deg, #00c853, #00a844); box-shadow: 0 4px 12px rgba(0,200,83,0.3); }}
      .promo-pill.hidden {{ background: linear-gradient(135deg, #7c4dff, #b388ff); box-shadow: 0 4px 12px rgba(124,77,255,0.3); }}
      .promo-cta {{
        display: flex; align-items: center; justify-content: space-between; gap: 10px;
        padding: 14px 16px; border-radius: 14px; text-decoration: none; color: #fff;
        background: linear-gradient(135deg, #0088cc 0%, #229ed9 100%);
        box-shadow: 0 6px 20px rgba(0,136,204,0.4);
        border: 1px solid rgba(255,255,255,0.15);
        margin-bottom: 14px;
      }}
      .promo-cta:active {{ transform: scale(0.98); }}
      .promo-cta .cta-left {{ display: flex; align-items: center; gap: 10px; min-width: 0; }}
      .promo-cta .ic {{
        width: 38px; height: 38px; border-radius: 50%;
        background: rgba(255,255,255,0.2);
        display: flex; align-items: center; justify-content: center; flex-shrink: 0;
      }}
      .promo-cta svg {{ width: 18px; height: 18px; fill: #fff; }}
      .promo-cta .cta-text {{ font-size: 14.5px; font-weight: 800; line-height: 1.3; }}
      .promo-cta .cta-text small {{ display: block; font-weight: 500; opacity: 0.9; font-size: 11px; margin-top: 2px; }}
      .promo-cta .arrow {{
        width: 26px; height: 26px; border-radius: 50%; background: rgba(255,255,255,0.18);
        display: flex; align-items: center; justify-content: center; flex-shrink: 0;
      }}
      .promo-cta .arrow svg {{ width: 13px; height: 13px; stroke: #fff; fill: none; stroke-width: 2.5; }}
      .promo-social {{ display: flex; align-items: center; justify-content: center; gap: 10px; }}
      .promo-social .avatars {{ display: flex; }}
      .promo-social .avatars span {{
        width: 26px; height: 26px; border-radius: 50%; display: flex; align-items: center;
        justify-content: center; font-size: 13px; border: 2px solid #1a0f2e; margin-left: -8px;
      }}
      .promo-social .avatars span:first-child {{ margin-left: 0; }}
      .promo-social .avatars span:nth-child(1) {{ background: #ffb74d; }}
      .promo-social .avatars span:nth-child(2) {{ background: #7c4dff; }}
      .promo-social .avatars span:nth-child(3) {{ background: #ff5e7d; }}
      .promo-social .avatars span:nth-child(4) {{ background: #00c853; font-size: 9px; font-weight: 800; color: #fff; }}
      .promo-social .count {{ font-size: 11.5px; font-weight: 700; color: #ffb74d; }}
      .footer {{ text-align: center; padding: 16px; font-size: 12px; color: #6ea8ff; }}
    </style>
    <script src="https://cdn.jsdelivr.net/npm/hls.js@latest"></script>
  </head>
  <body>
    <div class="card">
      <div class="header">
        <div class="icon"><svg viewBox="0 0 24 24"><path d="M12 3v12m0 0l4-4m-4 4l-4-4M5 21h14"/></svg></div>
        <div class="titles">
          <div class="t">{bot_username} | Video Downloader</div>
          <div class="s">Streaming in Telegram</div>
        </div>
      </div>

      <div class="player">
        <video id="v" playsinline></video>
        {f'<div class="badge quality">{quality}<span class="hd">HD</span></div>' if quality else ""}
        <div class="badge time" id="timeBadge">--:-- / --:--</div>
        <button class="center-play" id="centerPlay"><svg viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg></button>
        <div class="controls">
          <div class="seek-row">
            <span id="curTime">0:00</span>
            <input type="range" id="seek" min="0" max="100" value="0" step="0.1">
            <span id="durTime">0:00</span>
          </div>
          <div class="btn-row">
            <button id="playBtn" title="Play/Pause"><svg viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg></button>
            <button id="back10" title="-10s"><svg viewBox="0 0 24 24"><path d="M12 5V1L7 6l5 5V7a5 5 0 11-5 5H5a7 7 0 107-7z"/></svg></button>
            <button id="fwd10" title="+10s"><svg viewBox="0 0 24 24"><path d="M12 5V1l5 5-5 5V7a5 5 0 105 5h2a7 7 0 10-7-7z"/></svg></button>
            <div class="spacer"></div>
            <button id="muteBtn" title="Mute"><svg viewBox="0 0 24 24"><path d="M11 5L6 9H2v6h4l5 4V5zM19 5a11 11 0 010 14M15.5 8.5a6 6 0 010 7"/></svg></button>
            <button id="fsBtn" title="Fullscreen"><svg viewBox="0 0 24 24"><path d="M8 3H3v5M16 3h5v5M8 21H3v-5M16 21h5v-5"/></svg></button>
          </div>
        </div>
      </div>

      <div class="file-row">
        <div class="f-icon"><svg viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg></div>
        <div class="f-meta">
          <div class="f-name">{file_name}</div>
          <div class="f-size">{size_mb} MB</div>
        </div>
      </div>

      <div class="hint">
        <svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><path d="M12 16v-4M12 8h.01"/></svg>
        <div>If playback fails, the source may be temporarily unavailable.<br>Try again later.</div>
      </div>

      <div class="promo">
        <div class="promo-top">
          <div class="promo-flash">⚡ LIMITED TIME</div>
          <div class="promo-title">🔥 BIG DEALS LIVE NOW!</div>
          <div class="promo-sub">Up to <b>90% OFF</b> on Amazon, Flipkart, Myntra &amp; Ajio</div>
        </div>
        <div class="promo-body">
          <div class="promo-pills">
            <a class="promo-pill loot" href="{loot_deals_url}" target="_blank">🔥 Loot Deals</a>
            <a class="promo-pill error" href="{loot_deals_url}" target="_blank">$ Error Price</a>
            <a class="promo-pill hidden" href="{loot_deals_url}" target="_blank">🎁 Hidden Coupons</a>
          </div>
          <a class="promo-cta" href="{loot_deals_url}" target="_blank">
            <span class="cta-left">
              <span class="ic"><svg viewBox="0 0 24 24"><path d="M21 3L3 10.5l6.5 2.5L12 21l3-6 6-12z"/></svg></span>
              <span class="cta-text">Join Deal Channel<small>Best Deals &amp; Offers Daily</small></span>
            </span>
            <span class="arrow"><svg viewBox="0 0 24 24"><path d="M5 12h14M13 6l6 6-6 6"/></svg></span>
          </a>
          <div class="promo-social">
            <div class="avatars"><span>🧑</span><span>👩</span><span>🧔</span><span>99+</span></div>
            <div class="count">120K+ Smart Shoppers</div>
          </div>
        </div>
      </div>

      <div class="footer">@{bot_username}</div>
    </div>
    <script>
      const video = document.getElementById('v');
      const src = {proxied_m3u8!r};
      if (video.canPlayType('application/vnd.apple.mpegurl')) {{
        video.src = src;
      }} else if (window.Hls && Hls.isSupported()) {{
        const hls = new Hls({{ enableWorker: true, lowLatencyMode: true }});
        hls.loadSource(src);
        hls.attachMedia(video);
      }} else {{
        document.querySelector('.hint div').textContent = 'HLS not supported in this webview.';
      }}

      function fmt(t) {{
        if (!isFinite(t) || t < 0) t = 0;
        const m = Math.floor(t / 60), s = Math.floor(t % 60);
        return m + ':' + String(s).padStart(2, '0');
      }}
      function updateTimeBadge() {{
        document.getElementById('timeBadge').textContent = fmt(video.currentTime) + ' / ' + fmt(video.duration);
      }}
      const centerPlay = document.getElementById('centerPlay');
      const playBtn = document.getElementById('playBtn');
      const playIcon = '<svg viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg>';
      const pauseIcon = '<svg viewBox="0 0 24 24"><path d="M7 5h4v14H7zM13 5h4v14h-4z"/></svg>';
      function togglePlay() {{ video.paused ? video.play() : video.pause(); }}
      centerPlay.addEventListener('click', togglePlay);
      playBtn.addEventListener('click', togglePlay);
      video.addEventListener('play', () => {{
        centerPlay.style.display = 'none';
        playBtn.innerHTML = pauseIcon;
      }});
      video.addEventListener('pause', () => {{
        centerPlay.style.display = 'flex';
        playBtn.innerHTML = playIcon;
      }});
      video.addEventListener('loadedmetadata', () => {{
        document.getElementById('seek').max = video.duration || 0;
        document.getElementById('durTime').textContent = fmt(video.duration);
        updateTimeBadge();
      }});
      video.addEventListener('timeupdate', () => {{
        document.getElementById('seek').value = video.currentTime;
        document.getElementById('curTime').textContent = fmt(video.currentTime);
        updateTimeBadge();
      }});
      document.getElementById('seek').addEventListener('input', (e) => {{
        video.currentTime = Number(e.target.value);
      }});
      document.getElementById('back10').addEventListener('click', () => {{ video.currentTime = Math.max(0, video.currentTime - 10); }});
      document.getElementById('fwd10').addEventListener('click', () => {{ video.currentTime = Math.min(video.duration || 1e9, video.currentTime + 10); }});
      document.getElementById('muteBtn').addEventListener('click', () => {{ video.muted = !video.muted; }});
      document.getElementById('fsBtn').addEventListener('click', () => {{
        const el = document.querySelector('.player');
        if (document.fullscreenElement) document.exitFullscreen();
        else if (el.requestFullscreen) el.requestFullscreen();
      }});
    </script>
  </body>
</html>"""
    return Response(page, mimetype="text/html")


@bot.get("/hls")
async def hls_proxy():
    """
    Proxy + rewrite m3u8/segments to same-origin URLs to avoid WebView CORS issues.
    """
    u = request.args.get("u", "")
    if not u:
        return Response("Missing url", status=400)

    upstream = unquote_plus(u)
    async with aiohttp.ClientSession() as session:
        async with session.get(upstream) as resp:
            content_type = resp.headers.get("content-type", "")
            body = await resp.read()

    # If it's an m3u8, rewrite segment URLs to route back through this proxy.
    if "application/vnd.apple.mpegurl" in content_type or upstream.endswith(".m3u8"):
        try:
            text = body.decode("utf-8", errors="ignore")
        except Exception:
            return Response(body, content_type=content_type or "application/octet-stream")

        out_lines = []
        for line in text.splitlines():
            if not line or line.startswith("#"):
                out_lines.append(line)
                continue
            absolute = urljoin(upstream, line.strip())
            out_lines.append(f"/hls?u={quote_plus(absolute)}")

        return Response("\n".join(out_lines) + "\n", content_type="application/vnd.apple.mpegurl")

    # For .ts/.aac/.mp4 chunks etc, stream bytes as-is.
    return Response(body, content_type=content_type or "application/octet-stream")


@bot.get("/health")
async def health():
    return {"ok": True, "service": "diskwala-downloader-bot"}, 200


@bot.before_serving
async def before_serving():
    global mongo_client, mongo_db, users_col, payments_col, premium_reminder_task
    if MONGO_URI and AsyncIOMotorClient is not None:
        mongo_client = AsyncIOMotorClient(MONGO_URI)
        mongo_db = mongo_client[MONGO_DB_NAME]
        users_col = mongo_db["users"]
        payments_col = mongo_db["payments"]
        await users_col.create_index("bot_keys")
    else:
        logger.warning("MongoDB not configured or motor missing; premium persistence disabled.")
    await app.start()
    app.bot_key = _sanitize_bot_key(app.me.username, fallback_idx=1)
    await _notify_admin(app, f"✅ Bot @{app.me.username} started on server.")
    if premium_reminder_task is None or premium_reminder_task.done():
        premium_reminder_task = asyncio.create_task(_premium_reminder_loop(app))


@bot.after_serving
async def after_serving():
    global premium_reminder_task
    await _notify_admin(app, "⚠️ Bot is stopping.")
    if premium_reminder_task and not premium_reminder_task.done():
        premium_reminder_task.cancel()
        try:
            await premium_reminder_task
        except Exception:
            pass
    await app.stop()
    if mongo_client is not None:
        mongo_client.close()


# if __name__ == '__main__':

# bot.run(port=8000)
if __name__ == '__main__':
    loop = asyncio.get_event_loop()
    loop.create_task(bot.run_task(host='0.0.0.0', port=8080))
    loop.run_forever()
