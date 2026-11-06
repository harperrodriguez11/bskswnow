#!/usr/bin/env python3
"""
Bluesky auto-poster.

Coordination data (Credentials / Settings / PostPlan / LinkPlan / Report)
lives in a Google Sheet, read/written via the Sheets API v4. Media files
(images/videos) still live on Mega, accessed via rclone.

CAPTION MODES (new)
────────────────────────────────────────────────────
Controlled live from the Settings tab (or per-account via a Credentials
column with the same name):

  CAPTION_MODE = custom   -> always use the built-in generated adult/live-cam
                             body caption (the old behaviour; default).
  CAPTION_MODE = sheet    -> inherit the caption from the PostPlan / LinkPlan
                             "Caption" column for the row being posted.
  CAPTION_MODE = mixed    -> per post, pick "sheet" with probability
                             CAPTION_SHEET_PERCENTAGE (e.g. 50), otherwise
                             "custom".

  CAPTION_FALLBACK_TO_CUSTOM = true  -> if the sheet caption is empty for
                             that row, use a generated one instead of posting
                             without a caption. false = post with no caption.
  CAPTION_ENABLED = false    -> no body caption at all (link/hashtags only),
                             regardless of mode.

Everything else (link style, action line, hashtags, proxies, quota-aware
Sheets access, etc.) is unchanged. See the comments on each section.

SHEETS QUOTA DESIGN (summary)
  - batched reads (batchGet), batched writes (batchUpdate)
  - every call wrapped in sheets_call(): exponential backoff + jitter on
    429/5xx and on dead-connection errors (client is rebuilt)
  - startup jitter between parallel account jobs
  - a failed cycle never kills the job; it just waits for the next cycle

sheets_call() CONVENTION: it takes a zero-argument callable that builds the
request fresh on every attempt (a lambda), so a mid-retry client rebuild is
always picked up.
"""
import http.client
import io
import json
import os
import random
import re
import socket
import ssl
import subprocess
import sys
import time
import traceback
import uuid
from datetime import datetime
from urllib.parse import urljoin

import grapheme          # correct Bluesky grapheme counting
import requests
from bs4 import BeautifulSoup
from atproto import Client, models
from atproto_client.utils import TextBuilder
from atproto_client.request import Request as AtprotoRequest

from google.oauth2 import service_account
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError

RUN_TAG      = os.getenv("GITHUB_RUN_ID") or f"{socket.gethostname()}-{uuid.uuid4().hex[:8]}"
CLAIM_PREFIX = "CLAIMED_"

CURRENT_REPO     = os.getenv("GITHUB_REPOSITORY") or f"local-{socket.gethostname()}"
LOCK_TTL_MINUTES = 45   # business-level "which repo owns this account row" heartbeat TTL

# ═══════════════════════════════════════════════════════════════════════════
#  ENV / VALUE PARSING HELPERS
# ═══════════════════════════════════════════════════════════════════════════

def get_env(name, required=True, default=""):
    v = os.getenv(name)
    if v is None or not v.strip():
        if required:
            raise RuntimeError(f"Missing required env var: {name}")
        return default
    return v.strip()

def _parse_bool(raw, default=False):
    if raw is None or not str(raw).strip():
        return default
    return str(raw).strip().lower() in ("1", "true", "yes", "on")

def _parse_pct(raw, default):
    if raw is None or not str(raw).strip():
        return default
    raw = str(raw).strip().rstrip("%")
    try:
        v = float(raw)
        return v / 100.0 if v > 1 else v
    except ValueError:
        return default

def _parse_plain_float(raw, default):
    if raw is None or not str(raw).strip():
        return default
    try:
        return float(str(raw).strip())
    except ValueError:
        return default

def _parse_int(raw, default):
    if raw is None or not str(raw).strip():
        return default
    try:
        return max(1, int(str(raw).strip()))
    except ValueError:
        return default

def _parse_int_allow_zero(raw, default):
    if raw is None or not str(raw).strip():
        return default
    try:
        return max(0, int(float(str(raw).strip())))
    except ValueError:
        return default

def get_bool_env(name, default=False):
    return _parse_bool(os.getenv(name), default)

def get_float_env(name, default):
    return _parse_pct(os.getenv(name), default)

def get_int_env(name, default):
    return _parse_int(os.getenv(name), default)


# ═══════════════════════════════════════════════════════════════════════════
#  STATIC WORKFLOW KNOBS
# ═══════════════════════════════════════════════════════════════════════════

ACCOUNT_ROW = get_int_env("ACCOUNT_ROW", 1)   # 1-based data row (header is row 1 in the sheet)

RCLONE_CONFIG_PATH = get_env("RCLONE_CONFIG_PATH", required=False) or "rclone.conf"
RCLONE_REMOTE_NAME = get_env("RCLONE_REMOTE_NAME", required=False) or "mega"

CREDS_TAB    = "Credentials"
SETTINGS_TAB = "Settings"
REPORT_TAB   = "Report"
PROXIES_TAB  = "Proxies"

SKIP_STATUS_MARKERS = ("banned", "suspended", "taken down", "auth failed")

REPORT_HEADER = ["Timestamp (UTC)", "Handle", "Followers", "Gained", "Top Post", "Engagement", "Status"]

CREDENTIALS_HEADER = [
    "BSKY_HANDLE", "BSKY_APP_PW", "HASHTAGS",
    "MEGA_UPLOAD_FOLDER", "MEGA_PROCESSED_FOLDER",
    "LINK_URL", "LINK_DISPLAY_TEXT",
    "LOCKED_BY", "LOCKED_AT",
    "ACCOUNT_STATUS", "ACCOUNT_STATUS_AT",
    "ASSIGNED_REPO", "ASSIGNED_STATUS", "ASSIGNED_AT",
    "PROXY_IP", "PROXY_PORT", "PROXY_ASSIGNED_AT",
    "VIDEO_COUNT_TODAY", "VIDEO_COUNT_DATE",
]

PROXIES_BASE_HEADER = ["IP", "Port", "ResponseTime(s)", "Status"]
PROXY_TRACKING_COLUMNS = ["Status", "ASSIGNED_TO", "ASSIGNED_AT", "LAST_CHECKED", "LAST_CHECK_OK"]

DEFAULT_SETTINGS = [
    ("IMAGE_RATIO", "0.60"),
    ("VIDEO_RATIO", "0.40"),
    ("LINK_RATIO", "0.0"),
    ("HASHTAGS_ENABLED_IMAGE", "true"),
    ("HASHTAGS_ENABLED_VIDEO", "false"),
    ("HASHTAGS_ENABLED_LINK", "true"),
    ("LINK_ENABLED_IMAGE", "true"),
    ("LINK_ENABLED_VIDEO", "true"),
    ("LINK_PERCENTAGE", "1.0"),
    ("MAX_IMAGE_MB", "2.0"),
    ("CAPTION_ENABLED", "true"),
    # custom = generated captions | sheet = Caption column | mixed = random per post
    ("CAPTION_MODE", "custom"),
    # Only used when CAPTION_MODE=mixed: chance (0-100 or 0-1) of using the sheet caption.
    ("CAPTION_SHEET_PERCENTAGE", "50"),
    # If the sheet caption is empty: true = use a generated caption, false = post without one.
    ("CAPTION_FALLBACK_TO_CUSTOM", "true"),
    ("AUTO_CAPTION_ENABLED_LINK", "true"),
    ("PREVIEW_FETCH_TIMEOUT", "15"),
    ("MAX_THUMB_MB", "1.0"),
    ("ENABLE_REPORT", "false"),
    ("REPORT_TIMES_PER_DAY", "1"),
    ("TOP_POSTS_COUNT", "1"),
    ("TOP_POSTS_WITHIN", "30"),
    ("POST_PLAN_SHEET_NAME", "PostPlan"),
    ("LINK_PLAN_SHEET_NAME", "LinkPlan"),
    ("LOOP_INTERVAL_SECONDS", "1800"),
    ("MAX_ACCOUNTS_PER_RUN", ""),
    ("USE_PROXY", "true"),
    ("PROXY_REQUIRED", "true"),
    ("PROXY_CHECK_TIMEOUT_SECONDS", "10"),
    ("MAX_VIDEOS_PER_DAY", "0"),
    ("LINK_STYLE", "random"),
    ("LINK_DISPLAY_TEXT_ONLY", "false"),
    ("LINK_ON_NEW_LINE", "true"),
]

POSTED_STATUS_VALUE = "posted"
ASSIGN_STATUS_IN_USE = "In Use"

CAPTION_MODES = ("custom", "sheet", "mixed")

_URL_RE     = re.compile(r"https?://\S+")
_MENTION_RE = re.compile(r"@\S+")

REQUEST_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
}

CARDYB_EXTRACT_URL = "https://cardyb.bsky.app/v1/extract"
LINK_PREVIEW_MAX_RETRIES = 3
LINK_PREVIEW_RETRY_DELAY = 2

DEFAULT_LOOP_INTERVAL_SECONDS = 1800

PROXY_CHECK_URL = "https://bsky.social/xrpc/com.atproto.server.describeServer"


# ═══════════════════════════════════════════════════════════════════════════
#  RCLONE HELPERS (media files only — images/videos on Mega)
# ═══════════════════════════════════════════════════════════════════════════

def _rclone_run(args, timeout=120):
    return subprocess.run(
        ["rclone", "--config", RCLONE_CONFIG_PATH] + args,
        capture_output=True, text=True, timeout=timeout,
    )

def rclone_list_files(remote_folder):
    result = _rclone_run(["lsf", remote_folder, "--files-only"])
    if result.returncode != 0:
        print(f"Warning: rclone lsf failed for '{remote_folder}': {result.stderr.strip()[-300:]}")
        return []
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]

def rclone_claim(remote_folder, name):
    claimed_name = f"{CLAIM_PREFIX}{RUN_TAG}__{name}"
    result = _rclone_run(["moveto", f"{remote_folder}/{name}", f"{remote_folder}/{claimed_name}"])
    return claimed_name if result.returncode == 0 else None

def rclone_download(remote_folder, filename, local_path, timeout=120):
    result = _rclone_run(["copyto", f"{remote_folder}/{filename}", local_path], timeout=timeout)
    return result.returncode == 0

def rclone_move(src, dst, timeout=120):
    result = _rclone_run(["moveto", src, dst], timeout=timeout)
    return result.returncode == 0


# ═══════════════════════════════════════════════════════════════════════════
#  GOOGLE SHEETS: LOW-LEVEL CLIENT + QUOTA-AWARE RETRY WRAPPER
# ═══════════════════════════════════════════════════════════════════════════

GOOGLE_SHEET_ID                 = get_env("GOOGLE_SHEET_ID")
GOOGLE_APPLICATION_CREDENTIALS  = get_env("GOOGLE_APPLICATION_CREDENTIALS", required=False) or "google_creds.json"
SHEETS_RETRY_BUDGET_SECONDS     = get_int_env("SHEETS_RETRY_BUDGET_SECONDS", 240)
SHEETS_MAX_BACKOFF_SECONDS      = get_int_env("SHEETS_MAX_BACKOFF_SECONDS", 60)
START_JITTER_MAX_SECONDS        = get_int_env("START_JITTER_MAX_SECONDS", 45)
SHEETS_CALL_PACING_SECONDS      = _parse_plain_float(os.getenv("SHEETS_CALL_PACING_SECONDS"), 0.3)

_SCOPES = ["https://www.googleapis.com/auth/spreadsheets"]
_creds  = service_account.Credentials.from_service_account_file(
    GOOGLE_APPLICATION_CREDENTIALS, scopes=_SCOPES
)
_service = None
_sheets  = None


def _build_sheets_client():
    """(Re)build the googleapiclient service + spreadsheets() resource.
    Called at import and whenever a network-level error suggests the
    underlying connection is dead (common after a long sleep between cycles)."""
    global _service, _sheets
    _service = build("sheets", "v4", credentials=_creds, cache_discovery=False)
    _sheets  = _service.spreadsheets()


_build_sheets_client()

_NETWORK_TRANSIENT_EXCEPTIONS = (
    ssl.SSLError,
    ConnectionError,
    http.client.HTTPException,
    TimeoutError,
    socket.timeout,
    socket.error,
    OSError,
)


def _is_quota_error(exc):
    if not isinstance(exc, HttpError):
        return False
    status = getattr(exc.resp, "status", None)
    body = ""
    try:
        body = exc.content.decode("utf-8", "ignore") if isinstance(exc.content, bytes) else str(exc.content)
    except Exception:
        body = str(exc)
    return (
        status == 429
        or "RESOURCE_EXHAUSTED" in body
        or "rateLimitExceeded" in body
        or "Quota exceeded" in body
        or "quotaExceeded" in body
    )


def sheets_call(request_factory, budget_seconds=None):
    """Run a Sheets API request with exponential backoff + jitter on quota
    errors, transient 5xx, and raw network/SSL errors. `request_factory`
    MUST be a zero-arg callable (lambda) that builds the request fresh each
    attempt so a rebuilt client is always used."""
    budget = budget_seconds if budget_seconds is not None else SHEETS_RETRY_BUDGET_SECONDS
    start = time.time()
    attempt = 0
    while True:
        try:
            result = request_factory().execute()
            if SHEETS_CALL_PACING_SECONDS > 0:
                time.sleep(SHEETS_CALL_PACING_SECONDS)
            return result
        except HttpError as exc:
            status = getattr(exc.resp, "status", None)
            transient = _is_quota_error(exc) or status in (408, 429, 500, 502, 503, 504)
            if not transient:
                raise
            attempt += 1
            elapsed = time.time() - start
            if elapsed > budget:
                print(f"[sheets] giving up after {attempt} attempts / {elapsed:.0f}s "
                      f"(still hitting {'quota' if _is_quota_error(exc) else f'HTTP {status}'}).")
                raise
            delay = min(SHEETS_MAX_BACKOFF_SECONDS, 2 * (2 ** (attempt - 1))) + random.uniform(0, 1.5)
            kind = "quota" if _is_quota_error(exc) else f"HTTP {status}"
            print(f"[sheets] {kind} error (attempt {attempt}, {elapsed:.0f}s elapsed) — "
                  f"retrying in {delay:.1f}s…")
            time.sleep(delay)
        except _NETWORK_TRANSIENT_EXCEPTIONS as exc:
            attempt += 1
            elapsed = time.time() - start
            if elapsed > budget:
                print(f"[sheets] giving up after {attempt} attempts / {elapsed:.0f}s "
                      f"(still hitting network error: {exc!r}).")
                raise
            delay = min(SHEETS_MAX_BACKOFF_SECONDS, 2 * (2 ** (attempt - 1))) + random.uniform(0, 1.5)
            print(f"[sheets] network/connection error (attempt {attempt}, {elapsed:.0f}s elapsed): "
                  f"{exc!r} — rebuilding client and retrying in {delay:.1f}s…")
            try:
                _build_sheets_client()
            except Exception as rebuild_exc:
                print(f"[sheets] warning: failed to rebuild client ({rebuild_exc}); will retry anyway.")
            time.sleep(delay)


def qrange(tab, a1):
    safe = tab.replace("'", "''")
    return f"'{safe}'!{a1}"


def col_letter(n):
    letters = ""
    while n > 0:
        n, r = divmod(n - 1, 26)
        letters = chr(65 + r) + letters
    return letters


def sheets_get_batch(ranges):
    return sheets_call(
        lambda: _sheets.values().batchGet(
            spreadsheetId=GOOGLE_SHEET_ID, ranges=ranges,
            valueRenderOption="UNFORMATTED_VALUE",
        )
    )


def sheets_get(rng):
    return sheets_call(
        lambda: _sheets.values().get(
            spreadsheetId=GOOGLE_SHEET_ID, range=rng,
            valueRenderOption="UNFORMATTED_VALUE",
        )
    )


def sheets_update(rng, values):
    return sheets_call(
        lambda: _sheets.values().update(
            spreadsheetId=GOOGLE_SHEET_ID, range=rng,
            valueInputOption="USER_ENTERED", body={"values": values},
        )
    )


def sheets_batch_update_values(data):
    """data: list of {'range': A1_range, 'values': [[...]]}. One HTTP call."""
    if not data:
        return None
    return sheets_call(
        lambda: _sheets.values().batchUpdate(
            spreadsheetId=GOOGLE_SHEET_ID,
            body={"valueInputOption": "USER_ENTERED", "data": data},
        )
    )


def sheets_append(rng, values):
    return sheets_call(
        lambda: _sheets.values().append(
            spreadsheetId=GOOGLE_SHEET_ID, range=rng,
            valueInputOption="USER_ENTERED", insertDataOption="INSERT_ROWS",
            body={"values": values},
        )
    )


def sheets_existing_titles():
    meta = sheets_call(
        lambda: _sheets.get(spreadsheetId=GOOGLE_SHEET_ID, fields="sheets.properties.title")
    )
    return {s["properties"]["title"] for s in meta.get("sheets", [])}


REQUIRED_TABS = {
    CREDS_TAB:    CREDENTIALS_HEADER,
    SETTINGS_TAB: ["KEY", "VALUE"],
    REPORT_TAB:   REPORT_HEADER,
    PROXIES_TAB:  PROXIES_BASE_HEADER,
}


def ensure_required_tabs():
    """Create missing tabs (case/whitespace-insensitive match), one at a time,
    treating 'already exists' as a harmless no-op."""
    existing = sheets_existing_titles()
    existing_norm = {str(t).strip().lower() for t in existing}

    header_writes = []
    for tab, header in REQUIRED_TABS.items():
        if tab.strip().lower() in existing_norm:
            continue
        try:
            sheets_call(
                lambda t=tab: _sheets.batchUpdate(
                    spreadsheetId=GOOGLE_SHEET_ID,
                    body={"requests": [{"addSheet": {"properties": {"title": t}}}]},
                )
            )
            header_writes.append({"range": qrange(tab, "A1"), "values": [header]})
            print(f"Created missing tab: {tab}")
        except HttpError as exc:
            body = ""
            try:
                body = exc.content.decode("utf-8", "ignore") if isinstance(exc.content, bytes) else str(exc.content)
            except Exception:
                body = str(exc)
            if "already exists" in body:
                print(f"Note: tab '{tab}' already exists (under a slightly different name/case) — skipping creation.")
            else:
                raise
    if header_writes:
        sheets_batch_update_values(header_writes)


def ensure_extra_columns(tab, required_headers):
    """Append any missing headers as trailing columns; never touches existing data."""
    res = sheets_get(qrange(tab, "1:1"))
    rows = res.get("values", [])
    existing_header = rows[0] if rows else []
    existing_upper = {str(h).strip().upper() for h in existing_header if str(h).strip()}

    missing = [h for h in required_headers if h.upper() not in existing_upper]
    if not missing:
        return

    start_col = len(existing_header) + 1
    sheets_update(qrange(tab, f"{col_letter(start_col)}1"), [missing])
    print(f"Added missing column(s) to '{tab}': {missing}")


def ensure_settings_defaults():
    core = load_core_data(force=True)
    settings_existing = set(core["settings"].keys())
    missing_rows = [[k, v] for k, v in DEFAULT_SETTINGS if k not in settings_existing]
    if missing_rows:
        sheets_append(qrange(SETTINGS_TAB, "A:B"), missing_rows)
        print(f"Added {len(missing_rows)} missing default setting(s).")
        load_core_data(force=True)


# ═══════════════════════════════════════════════════════════════════════════
#  SHEET VALUE HELPERS
# ═══════════════════════════════════════════════════════════════════════════

def hmap(values):
    """Header map: {UPPERCASE_HEADER_NAME: 1-based column index}."""
    if not values:
        return {}
    header = {}
    for i, v in enumerate(values[0], start=1):
        if v is not None and str(v).strip():
            header[str(v).strip().upper()] = i
    return header

def cell(values, row, col):
    """1-based row/col lookup into a 2D list from batchGet (pads safely).
    NOTE: strips surrounding whitespace; internal newlines are preserved."""
    if col is None or row < 1 or row > len(values):
        return ""
    r = values[row - 1]
    if col > len(r):
        return ""
    v = r[col - 1]
    return str(v).strip() if v is not None else ""


# ═══════════════════════════════════════════════════════════════════════════
#  CYCLE-LEVEL DATA LOADING (batched, cached per cycle)
# ═══════════════════════════════════════════════════════════════════════════

_core_cache = None
_plan_cache = None


def load_core_data(force=False):
    """ONE batchGet call fetching Credentials + Settings + Report together."""
    global _core_cache
    if _core_cache is not None and not force:
        return _core_cache

    ranges = [qrange(CREDS_TAB, "A:ZZ"), qrange(SETTINGS_TAB, "A:ZZ"), qrange(REPORT_TAB, "A:ZZ")]
    res = sheets_get_batch(ranges)
    vr = res.get("valueRanges", [])

    def vals(i):
        return vr[i].get("values", []) if i < len(vr) else []

    creds_values, settings_values, report_values = vals(0), vals(1), vals(2)

    settings = {}
    for row in settings_values[1:]:
        if row and str(row[0]).strip():
            key = str(row[0]).strip().upper()
            val = str(row[1]).strip() if len(row) > 1 and row[1] is not None else ""
            settings[key] = val

    _core_cache = {"creds": creds_values, "settings": settings, "report": report_values}
    return _core_cache


def load_plan_data(post_plan_tab, link_plan_tab, force=False):
    """ONE batchGet call fetching PostPlan + LinkPlan together."""
    global _plan_cache
    key = (post_plan_tab, link_plan_tab)
    if _plan_cache is not None and _plan_cache["key"] == key and not force:
        return _plan_cache

    tabs = []
    if post_plan_tab:
        tabs.append(post_plan_tab)
    if link_plan_tab and link_plan_tab not in tabs:
        tabs.append(link_plan_tab)

    by_tab = {}
    if tabs:
        ranges = [qrange(t, "A:ZZ") for t in tabs]
        res = sheets_get_batch(ranges)
        vr = res.get("valueRanges", [])
        for t, r in zip(tabs, vr):
            by_tab[t] = r.get("values", [])

    _plan_cache = {"key": key, "by_tab": by_tab}
    return _plan_cache


# ═══════════════════════════════════════════════════════════════════════════
#  ACCOUNT CONFIG + LIVE SETTINGS
# ═══════════════════════════════════════════════════════════════════════════

_account_config = None


def load_global_settings(force_refresh=False):
    return load_core_data(force=force_refresh)["settings"]


def _normalize_caption_mode(raw):
    mode = (raw or "").strip().lower()
    aliases = {
        "generated": "custom", "auto": "custom", "own": "custom",
        "inherit": "sheet", "from_sheet": "sheet", "plan": "sheet",
        "both": "mixed", "random": "mixed", "mix": "mixed",
    }
    mode = aliases.get(mode, mode)
    return mode if mode in CAPTION_MODES else "custom"


def load_account_config(force_refresh=False):
    global _account_config

    if _account_config is not None and not force_refresh:
        return _account_config

    core = load_core_data(force=force_refresh)
    creds_values = core["creds"]
    header = hmap(creds_values)

    excel_row = ACCOUNT_ROW + 1
    if excel_row > len(creds_values):
        raise RuntimeError(
            f"ACCOUNT_ROW={ACCOUNT_ROW} but '{CREDS_TAB}' only has "
            f"{max(0, len(creds_values) - 1)} data row(s)."
        )

    def col(*names):
        for n in names:
            c = header.get(n.upper())
            if c is not None:
                return cell(creds_values, excel_row, c)
        return ""

    shared = core["settings"]
    def setting(key):
        # per-account Credentials column (if present and filled) overrides Settings tab
        return col(key) or shared.get(key, "")

    raw_link     = col("LINK_URL") or "https://foodiesposts.com"
    link_url     = raw_link if raw_link.startswith("http") else f"https://{raw_link}"
    link_display = col("LINK_DISPLAY_TEXT") or link_url.replace("https://", "").replace("http://", "")

    img_ratio_raw  = _parse_pct(setting("IMAGE_RATIO"), 0.60)
    vid_ratio_raw  = _parse_pct(setting("VIDEO_RATIO"), 0.40)
    link_ratio_raw = _parse_pct(setting("LINK_RATIO"), 0.0)
    ratio_sum      = img_ratio_raw + vid_ratio_raw + link_ratio_raw
    if ratio_sum > 0:
        image_ratio = img_ratio_raw / ratio_sum
        video_ratio = vid_ratio_raw / ratio_sum
        link_ratio  = link_ratio_raw / ratio_sum
    else:
        image_ratio, video_ratio, link_ratio = 0.60, 0.40, 0.0

    cfg = {
        "handle":                col("BSKY_HANDLE"),
        "app_pw":                col("BSKY_APP_PW"),
        "link_url":              link_url,
        "link_display_text":     link_display,
        "hashtags_raw":          col("HASHTAGS"),
        "mega_upload_folder":    col("MEGA_UPLOAD_FOLDER"),
        "mega_processed_folder": col("MEGA_PROCESSED_FOLDER"),
        "row_num":               ACCOUNT_ROW,

        "image_ratio":              image_ratio,
        "video_ratio":              video_ratio,
        "link_ratio":               link_ratio,
        "hashtags_enabled_image":   _parse_bool(setting("HASHTAGS_ENABLED_IMAGE"), True),
        "hashtags_enabled_video":   _parse_bool(setting("HASHTAGS_ENABLED_VIDEO"), False),
        "hashtags_enabled_link":    _parse_bool(setting("HASHTAGS_ENABLED_LINK"), True),
        "link_enabled_image":       _parse_bool(setting("LINK_ENABLED_IMAGE"), True),
        "link_enabled_video":       _parse_bool(setting("LINK_ENABLED_VIDEO"), True),
        "link_percentage":          _parse_pct(setting("LINK_PERCENTAGE"), 1.0),
        "max_image_bytes":          int(_parse_plain_float(setting("MAX_IMAGE_MB"), 2.0) * 1024 * 1024),

        # ── Caption behaviour ──────────────────────────────────────────────
        "caption_enabled":          _parse_bool(setting("CAPTION_ENABLED"), True),
        "caption_mode":             _normalize_caption_mode(setting("CAPTION_MODE")),
        "caption_sheet_percentage": _parse_pct(setting("CAPTION_SHEET_PERCENTAGE"), 0.5),
        "caption_fallback_custom":  _parse_bool(setting("CAPTION_FALLBACK_TO_CUSTOM"), True),
        "auto_caption_enabled_link": _parse_bool(setting("AUTO_CAPTION_ENABLED_LINK"), True),

        "preview_timeout":          _parse_int(setting("PREVIEW_FETCH_TIMEOUT"), 15),
        "max_thumb_bytes":          int(_parse_plain_float(setting("MAX_THUMB_MB"), 1.0) * 1024 * 1024),
        "enable_report":            _parse_bool(setting("ENABLE_REPORT"), False),
        "report_times_per_day":     _parse_int(setting("REPORT_TIMES_PER_DAY"), 1),
        "top_posts_count":          _parse_int(setting("TOP_POSTS_COUNT"), 1),
        "top_posts_within":         _parse_int(setting("TOP_POSTS_WITHIN"), 30),
        "post_plan_sheet_name":     setting("POST_PLAN_SHEET_NAME") or "PostPlan",
        "link_plan_sheet_name":     setting("LINK_PLAN_SHEET_NAME") or "LinkPlan",
        "loop_interval_seconds":    _parse_int(setting("LOOP_INTERVAL_SECONDS"),
                                                DEFAULT_LOOP_INTERVAL_SECONDS),

        "locked_by": col("LOCKED_BY"),
        "locked_at": col("LOCKED_AT"),
        "account_status": col("ACCOUNT_STATUS"),
        "has_lock_columns": ("LOCKED_BY" in header and "LOCKED_AT" in header),

        "use_proxy":            _parse_bool(setting("USE_PROXY"), True),
        "proxy_required":       _parse_bool(setting("PROXY_REQUIRED"), True),
        "proxy_check_timeout":  _parse_int(setting("PROXY_CHECK_TIMEOUT_SECONDS"), 10),
        "proxy_ip":             col("PROXY_IP"),
        "proxy_port":           col("PROXY_PORT"),
        "proxy_assigned_at":    col("PROXY_ASSIGNED_AT"),

        "max_videos_per_day":   _parse_int_allow_zero(setting("MAX_VIDEOS_PER_DAY"), 0),  # 0 = unlimited
        "link_style":           (setting("LINK_STYLE") or "random").strip().lower(),
        "link_display_text_only": _parse_bool(setting("LINK_DISPLAY_TEXT_ONLY"), False),
        "link_on_new_line":     _parse_bool(setting("LINK_ON_NEW_LINE"), True),
        "video_count_today":    col("VIDEO_COUNT_TODAY"),
        "video_count_date":     col("VIDEO_COUNT_DATE"),
    }

    if not cfg["handle"]:
        raise RuntimeError(
            f"BSKY_HANDLE is empty for account row {ACCOUNT_ROW} in '{CREDS_TAB}'."
        )

    _account_config = cfg
    return cfg

def _cfg():
    return load_account_config()

def refresh_account_config():
    return load_account_config(force_refresh=True)


# ═══════════════════════════════════════════════════════════════════════════
#  AUTO ACCOUNT-ROW ASSIGNMENT (fallback path when ACCOUNT_ROW isn't set)
# ═══════════════════════════════════════════════════════════════════════════

def resolve_account_row():
    explicit = get_env("ACCOUNT_ROW", required=False)
    if explicit:
        row = _parse_int(explicit, 1)
        print(f"ACCOUNT_ROW={row} was explicitly set — using it as a manual override "
              f"(auto-assignment skipped).")
        return row

    core = load_core_data(force=True)
    creds_values = core["creds"]
    header = hmap(creds_values)

    def hidx(*names):
        for n in names:
            if n.upper() in header:
                return header[n.upper()]
        return None

    handle_col = hidx("BSKY_HANDLE")
    repo_col   = hidx("ASSIGNED_REPO")
    status_col = hidx("ASSIGNED_STATUS")
    at_col     = hidx("ASSIGNED_AT")

    if handle_col is None or repo_col is None or status_col is None:
        raise RuntimeError(
            f"Auto row-assignment needs 'BSKY_HANDLE', 'ASSIGNED_REPO' and "
            f"'ASSIGNED_STATUS' columns in '{CREDS_TAB}'. Add any missing ones "
            f"to the header row, or set ACCOUNT_ROW manually for this run."
        )

    max_row = len(creds_values)

    for excel_row in range(2, max_row + 1):
        if cell(creds_values, excel_row, repo_col) == CURRENT_REPO:
            handle = cell(creds_values, excel_row, handle_col)
            data_idx = excel_row - 1
            print(f"Repo '{CURRENT_REPO}' already owns Credentials row {data_idx} "
                  f"({handle or 'no handle'}) — reusing it.")
            return data_idx

    for excel_row in range(2, max_row + 1):
        handle_val = cell(creds_values, excel_row, handle_col)
        status_val = cell(creds_values, excel_row, status_col)
        if not handle_val:
            continue
        if status_val.lower() == ASSIGN_STATUS_IN_USE.lower():
            continue

        now = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        data = [
            {"range": qrange(CREDS_TAB, f"{col_letter(repo_col)}{excel_row}"), "values": [[CURRENT_REPO]]},
            {"range": qrange(CREDS_TAB, f"{col_letter(status_col)}{excel_row}"), "values": [[ASSIGN_STATUS_IN_USE]]},
        ]
        if at_col is not None:
            data.append({"range": qrange(CREDS_TAB, f"{col_letter(at_col)}{excel_row}"), "values": [[now]]})
        sheets_batch_update_values(data)

        data_idx = excel_row - 1
        print(f"Claimed Credentials row {data_idx} ({handle_val}) for repo '{CURRENT_REPO}'.")
        return data_idx

    raise RuntimeError(
        f"No available account rows left in '{CREDS_TAB}' — every configured "
        f"row is already marked '{ASSIGN_STATUS_IN_USE}'. Add a new account "
        f"row, or clear ASSIGNED_REPO/ASSIGNED_STATUS on one you want to free up."
    )


# ═══════════════════════════════════════════════════════════════════════════
#  CROSS-REPO SOFT LOCK
# ═══════════════════════════════════════════════════════════════════════════

class AccountLockedElsewhereError(Exception):
    """Non-fatal — another repo currently owns this account row."""


def try_acquire_account_lock():
    global _account_config

    core = load_core_data(force=True)
    creds_values = core["creds"]
    header = hmap(creds_values)
    by_col = header.get("LOCKED_BY")
    at_col = header.get("LOCKED_AT")
    excel_row = ACCOUNT_ROW + 1

    if by_col is None or at_col is None:
        return True

    locked_by     = cell(creds_values, excel_row, by_col)
    locked_at_raw = cell(creds_values, excel_row, at_col)

    stale = True
    if locked_at_raw:
        try:
            locked_at = time.mktime(time.strptime(locked_at_raw, "%Y-%m-%dT%H:%M:%SZ"))
            stale = (time.time() - locked_at) > LOCK_TTL_MINUTES * 60
        except ValueError:
            stale = True

    if locked_by and locked_by != CURRENT_REPO and not stale:
        print(f"Row {ACCOUNT_ROW} is currently locked by '{locked_by}' "
              f"(last heartbeat {locked_at_raw} UTC, TTL {LOCK_TTL_MINUTES}m). Skipping this run.")
        return False

    now = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    sheets_batch_update_values([
        {"range": qrange(CREDS_TAB, f"{col_letter(by_col)}{excel_row}"), "values": [[CURRENT_REPO]]},
        {"range": qrange(CREDS_TAB, f"{col_letter(at_col)}{excel_row}"), "values": [[now]]},
    ])
    if _account_config:
        _account_config["locked_by"] = CURRENT_REPO
        _account_config["locked_at"] = now
    return True


def _write_account_status(status):
    global _account_config

    core = load_core_data(force=True)
    header = hmap(core["creds"])
    status_col = header.get("ACCOUNT_STATUS")
    if status_col is None:
        print("Note: no ACCOUNT_STATUS column in Credentials — add one to track per-row status.")
        return
    at_col = header.get("ACCOUNT_STATUS_AT")
    excel_row = ACCOUNT_ROW + 1

    data = [{"range": qrange(CREDS_TAB, f"{col_letter(status_col)}{excel_row}"), "values": [[status]]}]
    if at_col is not None:
        data.append({"range": qrange(CREDS_TAB, f"{col_letter(at_col)}{excel_row}"), "values": [[_now_str()]]})

    try:
        sheets_batch_update_values(data)
        if _account_config:
            _account_config["account_status"] = status
        print(f"Credentials ACCOUNT_STATUS set to '{status}' for row {ACCOUNT_ROW}.")
    except Exception as exc:
        print(f"Warning: could not update ACCOUNT_STATUS: {exc}")


# ═══════════════════════════════════════════════════════════════════════════
#  PROXIES
# ═══════════════════════════════════════════════════════════════════════════

class NoProxyAvailableError(Exception):
    """No live, unused proxy could be found this cycle (and PROXY_REQUIRED is true)."""


def _http_proxy_url(ip, port):
    return f"http://{ip}:{port}"


def check_proxy_alive(ip, port, timeout=10):
    """Alive = can actually reach Bluesky's PDS through the proxy."""
    proxy_url = _http_proxy_url(ip, port)
    try:
        resp = requests.get(
            PROXY_CHECK_URL,
            proxies={"http": proxy_url, "https": proxy_url},
            timeout=timeout,
        )
        return resp.status_code < 500
    except Exception:
        return False


def _load_proxies_values():
    res = sheets_get(qrange(PROXIES_TAB, "A:ZZ"))
    return res.get("values", [])


def _proxy_cols(values):
    header = hmap(values)
    def ci(*names):
        for n in names:
            if n.upper() in header:
                return header[n.upper()]
        return None
    return {
        "ip":           ci("IP"),
        "port":         ci("PORT"),
        "status":       ci("STATUS"),
        "rt":           ci("RESPONSETIME(S)", "RESPONSE TIME(S)", "RESPONSETIME"),
        "assigned_to":  ci("ASSIGNED_TO"),
        "assigned_at":  ci("ASSIGNED_AT"),
        "last_checked": ci("LAST_CHECKED"),
        "last_ok":      ci("LAST_CHECK_OK"),
    }


def _write_proxy_row(excel_row, cols, updates):
    data = []
    for key, val in updates.items():
        col = cols.get(key)
        if col is None:
            continue
        data.append({"range": qrange(PROXIES_TAB, f"{col_letter(col)}{excel_row}"), "values": [[val]]})
    if data:
        sheets_batch_update_values(data)


def _find_proxy_row(ip, port):
    values = _load_proxies_values()
    cols = _proxy_cols(values)
    if cols["ip"] is None:
        return None, None, None
    for excel_row in range(2, len(values) + 1):
        if cell(values, excel_row, cols["ip"]) == ip and cell(values, excel_row, cols["port"]) == port:
            return excel_row, cols, values
    return None, None, None


def _proxy_owned_by(ip, port, handle):
    """True only if the Proxies tab shows THIS handle as ASSIGNED_TO owner."""
    excel_row, cols, values = _find_proxy_row(ip, port)
    if excel_row is None or cols["assigned_to"] is None:
        return False
    assigned_to = cell(values, excel_row, cols["assigned_to"])
    if not assigned_to:
        return False
    return assigned_to.strip().lower() == handle.strip().lower()


def touch_proxy_alive(ip, port):
    excel_row, cols, _values = _find_proxy_row(ip, port)
    if excel_row is None:
        return
    _write_proxy_row(excel_row, cols, {"last_checked": _now_str(), "last_ok": "alive"})


def release_or_kill_proxy(ip, port, alive):
    """alive=False: mark 'dead'. alive=True: release back to the free pool."""
    excel_row, cols, _values = _find_proxy_row(ip, port)
    if excel_row is None:
        return
    now = _now_str()
    if alive:
        _write_proxy_row(excel_row, cols, {
            "status": "", "assigned_to": "", "assigned_at": "",
            "last_checked": now, "last_ok": "alive",
        })
    else:
        _write_proxy_row(excel_row, cols, {
            "status": "dead", "last_checked": now, "last_ok": "dead",
        })


def _claim_proxy_row(cols, excel_row, handle):
    """Optimistic claim: re-read Status (or ASSIGNED_TO) right before writing."""
    if cols["status"] is not None:
        rng = qrange(PROXIES_TAB, f"{col_letter(cols['status'])}{excel_row}")
        fresh = sheets_get(rng)
        rows = fresh.get("values", [])
        current = str(rows[0][0]).strip().lower() if rows and rows[0] else ""
        if current in ("assigned", "dead"):
            return False
    elif cols["assigned_to"] is not None:
        rng = qrange(PROXIES_TAB, f"{col_letter(cols['assigned_to'])}{excel_row}")
        fresh = sheets_get(rng)
        rows = fresh.get("values", [])
        current = str(rows[0][0]).strip() if rows and rows[0] else ""
        if current:
            return False

    now = _now_str()
    _write_proxy_row(excel_row, cols, {
        "status": "assigned", "assigned_to": handle, "assigned_at": now,
        "last_checked": now, "last_ok": "alive",
    })
    return True


def find_and_claim_free_proxy(handle, timeout):
    values = _load_proxies_values()
    if not values or len(values) < 2:
        return None
    cols = _proxy_cols(values)
    if cols["ip"] is None or cols["port"] is None:
        print(f"Warning: '{PROXIES_TAB}' needs at least IP and Port columns.")
        return None

    candidates = []
    for excel_row in range(2, len(values) + 1):
        ip = cell(values, excel_row, cols["ip"])
        port = cell(values, excel_row, cols["port"])
        if not ip or not port:
            continue
        status = cell(values, excel_row, cols["status"]).lower() if cols["status"] else ""
        last_ok = cell(values, excel_row, cols["last_ok"]).lower() if cols["last_ok"] else ""
        assigned_to = cell(values, excel_row, cols["assigned_to"]).strip() if cols["assigned_to"] else ""
        if status in ("assigned", "dead"):
            continue
        if last_ok == "dead":
            continue
        if assigned_to:
            continue
        rt = 999.0
        if cols["rt"]:
            raw_rt = cell(values, excel_row, cols["rt"])
            try:
                rt = float(raw_rt) if raw_rt else 999.0
            except ValueError:
                rt = 999.0
        candidates.append((rt, excel_row, ip, port))

    candidates.sort(key=lambda t: t[0])

    for _, excel_row, ip, port in candidates:
        if check_proxy_alive(ip, port, timeout):
            if _claim_proxy_row(cols, excel_row, handle):
                print(f"Claimed proxy {ip}:{port} for {handle}.")
                return ip, port
            print(f"Lost claim race on proxy {ip}:{port} — trying next candidate.")
            continue
        _write_proxy_row(excel_row, cols, {"status": "dead", "last_checked": _now_str(), "last_ok": "dead"})
        print(f"Proxy {ip}:{port} failed liveness check — marked dead, trying next candidate.")

    return None


def _write_account_proxy(ip, port):
    global _account_config
    core = load_core_data(force=True)
    header = hmap(core["creds"])
    ip_col   = header.get("PROXY_IP")
    port_col = header.get("PROXY_PORT")
    at_col   = header.get("PROXY_ASSIGNED_AT")
    if ip_col is None or port_col is None:
        print(f"Warning: '{CREDS_TAB}' needs PROXY_IP and PROXY_PORT columns to "
              f"persist the proxy assignment across cycles.")
        return
    excel_row = ACCOUNT_ROW + 1
    data = [
        {"range": qrange(CREDS_TAB, f"{col_letter(ip_col)}{excel_row}"), "values": [[ip]]},
        {"range": qrange(CREDS_TAB, f"{col_letter(port_col)}{excel_row}"), "values": [[port]]},
    ]
    if at_col is not None:
        data.append({"range": qrange(CREDS_TAB, f"{col_letter(at_col)}{excel_row}"), "values": [[_now_str()]]})
    sheets_batch_update_values(data)
    if _account_config:
        _account_config["proxy_ip"] = ip
        _account_config["proxy_port"] = port


def _clear_account_proxy():
    global _account_config
    core = load_core_data(force=True)
    header = hmap(core["creds"])
    ip_col   = header.get("PROXY_IP")
    port_col = header.get("PROXY_PORT")
    if ip_col is None or port_col is None:
        return
    excel_row = ACCOUNT_ROW + 1
    sheets_batch_update_values([
        {"range": qrange(CREDS_TAB, f"{col_letter(ip_col)}{excel_row}"), "values": [[""]]},
        {"range": qrange(CREDS_TAB, f"{col_letter(port_col)}{excel_row}"), "values": [[""]]},
    ])
    if _account_config:
        _account_config["proxy_ip"] = ""
        _account_config["proxy_port"] = ""


def ensure_account_proxy(cfg):
    """Keep the account on its assigned proxy while alive; otherwise kill it
    and claim a fresh one. Returns 'http://ip:port' or None if disabled."""
    if not cfg.get("use_proxy", True):
        return None

    handle  = cfg["handle"]
    timeout = cfg.get("proxy_check_timeout", 10)

    ip, port = cfg.get("proxy_ip", ""), cfg.get("proxy_port", "")
    if ip and port:
        if not _proxy_owned_by(ip, port, handle):
            print(f"Proxy {ip}:{port} on file for {handle} is not exclusively assigned to "
                  f"this account in '{PROXIES_TAB}' — clearing the stale record and "
                  f"claiming a fresh, unshared proxy instead.")
            _clear_account_proxy()
        elif check_proxy_alive(ip, port, timeout):
            touch_proxy_alive(ip, port)
            print(f"Reusing existing proxy {ip}:{port} for {handle} (still alive).")
            return _http_proxy_url(ip, port)
        else:
            print(f"Assigned proxy {ip}:{port} for {handle} is dead — releasing it and picking a new one.")
            release_or_kill_proxy(ip, port, alive=False)
            _clear_account_proxy()

    claimed = find_and_claim_free_proxy(handle, timeout)
    if claimed is None:
        if cfg.get("proxy_required", True):
            raise NoProxyAvailableError(
                f"No live, unused proxy available in '{PROXIES_TAB}' for {handle}."
            )
        print("No proxy available and PROXY_REQUIRED is false — continuing without a proxy.")
        return None

    ip, port = claimed
    _write_account_proxy(ip, port)
    return _http_proxy_url(ip, port)


class ProxyClientBuildError(Exception):
    """A proxy was required but could not be attached to the atproto Client.
    Never fall back to posting without a proxy."""


def build_bsky_client(proxy_url):
    """Create the atproto Client routed through `proxy_url` if given.
    atproto's Client doesn't forward kwargs to httpx, so we build the
    underlying Request ourselves and pass it in."""
    if not proxy_url:
        return Client()

    last_exc = None
    for kwargs in (
        {"proxy": proxy_url},
        {"proxies": {"http://": proxy_url, "https://": proxy_url}},
    ):
        try:
            req = AtprotoRequest(**kwargs)
            try:
                req._client.timeout = 120.0
            except Exception:
                pass
            return Client(request=req)
        except TypeError as exc:
            last_exc = exc
            continue

    raise ProxyClientBuildError(
        f"Could not configure HTTP proxy {proxy_url!r} on the atproto Client "
        f"with the installed httpx/atproto version ({last_exc})."
    )


def _looks_like_proxy_error(exc):
    text = f"{type(exc).__name__}: {exc}"
    markers = (
        "ProxyError", "ConnectError", "ConnectTimeout", "ReadTimeout",
        "Failed to establish a new connection", "Connection refused",
        "Cannot connect to proxy", "Tunnel connection failed",
        "Max retries exceeded", "RemoteProtocolError", "ConnectionResetError",
    )
    return any(m in text for m in markers)


# ═══════════════════════════════════════════════════════════════════════════
#  TEXT HELPERS
# ═══════════════════════════════════════════════════════════════════════════

def _posting_handle():
    h = _cfg()["handle"]
    return h if h.startswith("@") else f"@{h}"

def replace_mentions(text):
    return _MENTION_RE.sub(_posting_handle(), text) if text else text

def replace_urls(text):
    return _URL_RE.sub(_cfg()["link_url"], text) if text else text


# ═══════════════════════════════════════════════════════════════════════════
#  CONFIG SUMMARY
# ═══════════════════════════════════════════════════════════════════════════

def print_config_summary():
    cfg = _cfg()
    print("── Run config (live from Settings + Credentials in Google Sheets) ──")
    print(f"  Account row:              {cfg['row_num']}  ({_posting_handle()})")
    print(f"  Account status:           {cfg.get('account_status') or '(not set)'}")
    print(f"  Mega upload folder:       {cfg['mega_upload_folder'] or '(not set!)'}")
    print(f"  Mega processed folder:    {cfg['mega_processed_folder'] or '(not set!)'}")
    print(f"  Post link (in-caption):   {cfg['link_display_text']} -> {cfg['link_url']}")
    print(f"  Post-type mix:            image {cfg['image_ratio']:.0%} / "
          f"video {cfg['video_ratio']:.0%} / previewLink {cfg['link_ratio']:.0%}")
    print(f"  Caption enabled:          {cfg['caption_enabled']}")
    mode = cfg["caption_mode"]
    if mode == "mixed":
        print(f"  Caption mode:             mixed ({cfg['caption_sheet_percentage']:.0%} sheet / "
              f"{1 - cfg['caption_sheet_percentage']:.0%} custom)")
    else:
        print(f"  Caption mode:             {mode} "
              f"({'inherit from sheet Caption column' if mode == 'sheet' else 'built-in generated captions'})")
    print(f"  Empty sheet caption →     "
          f"{'use generated caption' if cfg['caption_fallback_custom'] else 'post without caption'}")
    print(f"  Hashtags on image posts:  {cfg['hashtags_enabled_image']}")
    print(f"  Hashtags on video posts:  {cfg['hashtags_enabled_video']}")
    print(f"  Hashtags on previewLink:  {cfg['hashtags_enabled_link']}")
    print(f"  Link on image posts:      {cfg['link_enabled_image']}")
    print(f"  Link on video posts:      {cfg['link_enabled_video']}")
    print(f"  Link inclusion rate:      {cfg['link_percentage']:.0%} of eligible image/video posts")
    print(f"  Max image size:           {cfg['max_image_bytes']/(1024*1024):.2f} MB")
    print(f"  previewLink auto-caption: {cfg['auto_caption_enabled_link']} (generated caption when sheet has none)")
    print(f"  previewLink fetch timeout:{cfg['preview_timeout']}s")
    print(f"  previewLink max thumb:    {cfg['max_thumb_bytes']/(1024*1024):.2f} MB")
    print(f"  Loop interval:            {cfg['loop_interval_seconds']}s ({cfg['loop_interval_seconds']/60:.1f} min)")
    print(f"  Generate report:          {cfg['enable_report']}")
    if cfg["enable_report"]:
        print(f"  Report frequency:         {cfg['report_times_per_day']}x per 24h")
        print(f"  Top posts combined:       {cfg['top_posts_count']}")
        print(f"  Scan last N posts:        {cfg['top_posts_within']}")
    print(f"  Post-plan sheet (media):  {cfg['post_plan_sheet_name']}")
    print(f"  LinkPlan sheet:           {cfg['link_plan_sheet_name']}")
    print(f"  Config source:            Google Sheet ({GOOGLE_SHEET_ID})")
    if cfg.get("has_lock_columns"):
        print(f"  Cross-repo lock:          enabled (owner={cfg.get('locked_by') or '—'}, "
              f"last heartbeat={cfg.get('locked_at') or '—'})")
    else:
        print("  Cross-repo lock:          disabled (add LOCKED_BY / LOCKED_AT columns to enable)")
    print(f"  Proxy usage:              {'enabled' if cfg.get('use_proxy', True) else 'disabled'}"
          f"{' (required)' if cfg.get('use_proxy', True) and cfg.get('proxy_required', True) else ''}")
    if cfg.get("use_proxy", True):
        proxy_display = f"{cfg.get('proxy_ip') or '—'}:{cfg.get('proxy_port') or '—'}"
        print(f"  Current proxy:            {proxy_display}")
        print(f"  Proxy check timeout:      {cfg.get('proxy_check_timeout', 10)}s")
    max_v = cfg.get("max_videos_per_day", 0)
    if max_v > 0:
        used = get_video_count_today()
        print(f"  Video daily limit:        {used}/{max_v} (UTC day)")
    else:
        print(f"  Video daily limit:        unlimited")
    print(f"  Link style:               {cfg.get('link_style', 'random')}"
          f"{' (custom display text only)' if cfg.get('link_display_text_only') else ''}")
    print(f"  Link placement:           {'new line' if cfg.get('link_on_new_line', True) else 'inline with caption'}")
    print(f"  Sheets retry budget:      {SHEETS_RETRY_BUDGET_SECONDS}s per call "
          f"(max backoff {SHEETS_MAX_BACKOFF_SECONDS}s)")
    print("─────────────────────────────────────────────────")


# ═══════════════════════════════════════════════════════════════════════════
#  REPORT TAB
# ═══════════════════════════════════════════════════════════════════════════

def _now_str():
    return time.strftime("%Y-%m-%d %H:%M", time.gmtime()) + " UTC"

def _parse_report_ts(s):
    try:
        return time.mktime(time.strptime(s.replace(" UTC", ""), "%Y-%m-%d %H:%M"))
    except Exception:
        return None


def _normalize_handle(h):
    return (h or "").strip().lstrip("@").lower()


def _sanitize_report_text(s, max_len=200):
    if s is None:
        return ""
    text = re.sub(r"[\r\n\t]+", " ", str(s))
    text = re.sub(r" {2,}", " ", text).strip()
    if len(text) > max_len:
        text = text[: max_len - 1] + "…"
    return text


def ensure_report_header():
    """Make sure Report!A1:G1 is exactly REPORT_HEADER."""
    res = sheets_get(qrange(REPORT_TAB, "1:1"))
    rows = res.get("values", [])
    existing = [str(c).strip() if c is not None else "" for c in (rows[0] if rows else [])]
    existing_norm = (existing + [""] * 7)[:7]
    expected = list(REPORT_HEADER)
    if existing_norm == expected:
        return
    sheets_update(qrange(REPORT_TAB, "A1:G1"), [expected])
    print(f"Report header repaired to: {expected}")


def _next_report_row():
    res = sheets_get(qrange(REPORT_TAB, "A:A"))
    values = res.get("values", [])
    for i, row in enumerate(values):
        if i == 0:
            continue
        cell0 = str(row[0]).strip() if row and row[0] is not None else ""
        if not cell0:
            return i + 1
    return len(values) + 1


def _last_report_for_handle(handle):
    report_values = load_core_data()["report"]
    target = _normalize_handle(handle)
    for r in range(len(report_values), 1, -1):
        h = cell(report_values, r, 2)
        if _normalize_handle(h) == target:
            ts = cell(report_values, r, 1)
            followers = None
            f_raw = cell(report_values, r, 3)
            if f_raw:
                try:
                    followers = int(float(f_raw))
                except ValueError:
                    followers = None
            return ts, followers
    return None, None


def _report_due(handle, times_per_day):
    times_per_day = max(1, times_per_day)
    last_ts, _ = _last_report_for_handle(handle)
    if last_ts is None:
        return True
    last_epoch = _parse_report_ts(last_ts)
    if last_epoch is None:
        return True
    interval_seconds = 86400.0 / times_per_day
    return (time.time() - last_epoch) >= interval_seconds


def _append_report(rows):
    """Write report rows into exact A–G columns (explicit next-row update,
    not values.append, so data can't drift into extra columns)."""
    if not rows:
        return
    ensure_report_header()
    start_row = _next_report_row()
    clean = []
    for row in rows:
        r = list(row) + [""] * 7
        r = r[:7]
        ts       = str(r[0] or "")
        handle   = str(r[1] or "").lstrip("@")
        try:
            followers = int(float(r[2])) if str(r[2]).strip() != "" else ""
        except (ValueError, TypeError):
            followers = str(r[2] or "")
        try:
            gained = int(float(r[3])) if str(r[3]).strip() != "" else ""
        except (ValueError, TypeError):
            gained = str(r[3] or "")
        top_post = _sanitize_report_text(r[4], max_len=250)
        try:
            engagement = int(float(r[5])) if str(r[5]).strip() != "" else ""
        except (ValueError, TypeError):
            engagement = str(r[5] or "")
        status = str(r[6] or "")
        clean.append([ts, handle, followers, gained, top_post, engagement, status])

    end_row = start_row + len(clean) - 1
    rng = qrange(REPORT_TAB, f"A{start_row}:G{end_row}")
    sheets_update(rng, clean)
    load_core_data(force=True)
    print(f"Report row(s) written to {REPORT_TAB}!A{start_row}:G{end_row}")


def _top_post_summary(client, handle, top_n, within):
    try:
        response = client.get_author_feed(actor=handle, limit=within)
    except Exception as exc:
        return f"(couldn't fetch posts: {exc})", 0

    posts = []
    for item in response.feed:
        if getattr(item, "reason", None) is not None:
            continue
        p       = item.post
        likes   = getattr(p, "like_count",   0) or 0
        reposts = getattr(p, "repost_count", 0) or 0
        replies = getattr(p, "reply_count",  0) or 0
        quotes  = getattr(p, "quote_count",  0) or 0
        try:
            text = p.record.text or ""
        except AttributeError:
            text = ""
        posts.append({
            "text": text, "likes": likes, "reposts": reposts,
            "replies": replies, "quotes": quotes,
            "engagement": likes + reposts + replies + quotes,
        })

    if not posts:
        return "(no posts found)", 0

    ranked = sorted(posts, key=lambda p: p["engagement"], reverse=True)[:max(1, top_n)]

    if len(ranked) == 1:
        p = ranked[0]
        preview = _sanitize_report_text(p["text"], max_len=100)
        return preview, p["engagement"]

    parts = []
    for i, p in enumerate(ranked, start=1):
        preview = _sanitize_report_text(p["text"], max_len=60)
        parts.append(f"{i}) {preview} ({p['engagement']})")
    return " | ".join(parts), ranked[0]["engagement"]


def generate_report(client, handle, cfg):
    if not _report_due(handle, cfg["report_times_per_day"]):
        print(f"Report for {handle} not due yet (limit: {cfg['report_times_per_day']}x/24h).")
        return
    try:
        profile = client.get_profile(actor=handle)
        total   = int(profile.followers_count or 0)

        _, prev_followers = _last_report_for_handle(handle)
        prev   = prev_followers if prev_followers is not None else total
        gained = total - prev

        top_preview, top_engagement = _top_post_summary(
            client, handle, cfg["top_posts_count"], cfg["top_posts_within"]
        )

        row = [
            _now_str(),
            handle.lstrip("@"),
            total,
            gained,
            top_preview,
            int(top_engagement or 0),
            "OK",
        ]
        _append_report([row])
        print(f"Report logged for {handle}: {total} followers ({gained:+d} since last), "
              f"top post engagement={top_engagement}.")
    except Exception as exc:
        print(f"Warning: report generation failed: {exc}")
        traceback.print_exc()


def run_report(client, handle, cfg):
    try:
        generate_report(client, handle, cfg)
    except Exception as exc:
        print(f"Warning: report generation failed: {exc}")


# ═══════════════════════════════════════════════════════════════════════════
#  ERROR TYPES
# ═══════════════════════════════════════════════════════════════════════════

class AccountTakenDownError(Exception):
    """Fatal — log to sheet, disable workflow."""

class NoMediaFoundError(Exception):
    """Clean exit (code 0) — nothing postable this cycle."""

class NoPreviewError(Exception):
    """Link-preview metadata could not be fetched via cardyb or manual scrape."""


def log_account_problem(handle, status):
    try:
        _append_report([[_now_str(), handle, "", "", "", "", status]])
        print(f"Logged '{status}' for {handle}.")
    except Exception as exc:
        print(f"Warning: could not log account status: {exc}")


# ═══════════════════════════════════════════════════════════════════════════
#  ACCOUNT DISPLAY
# ═══════════════════════════════════════════════════════════════════════════

def print_target_account(handle):
    display = handle if handle.startswith("@") else f"@{handle}"
    print(f"Target Bluesky account: {display}")
    print(f"  (app password: {'loaded' if _cfg().get('app_pw') else 'MISSING!'})")


# ═══════════════════════════════════════════════════════════════════════════
#  HASHTAGS
# ═══════════════════════════════════════════════════════════════════════════

def get_account_hashtags():
    raw = _cfg().get("hashtags_raw", "")
    if raw:
        tags = [w.lstrip("#") for w in raw.split() if w.startswith("#")]
        if tags:
            return tags
    try:
        with open("hashtags.txt", "r", encoding="utf-8") as f:
            sets = [l.strip() for l in f if l.strip()]
        return [w.lstrip("#") for w in random.choice(sets).split() if w.startswith("#")] if sets else []
    except FileNotFoundError:
        return []


# ═══════════════════════════════════════════════════════════════════════════
#  CAPTIONS: GENERATED ("custom") + SHEET-INHERITED ("sheet") + "mixed"
# ═══════════════════════════════════════════════════════════════════════════
# Post layout (every media post):
#
#   <body caption — generated OR from the sheet>
#
#   💖 <action words> 😘 <rich "Live Models"  OR  plain actual URL>
#
#   #hashtag1 #hashtag2 ...
#
# Link is ONLY one style per post — never rich + plain together.

_CAPTION_EMOJIS = [
    "🔥", "😈", "💋", "🥵", "💦", "🍑", "🍆", "❤️‍🔥", "😉", "👅",
    "💃", "🎥", "🔴", "💕", "✨", "👀", "🥰", "😏", "💖", "🌙", "😘",
]

_BODY_CAPTION_TEMPLATES = [
    "I'm owning my body without a single thread in the way. These nipples are hard and ready for attention. {e}",
    "No clothes, no rules — just me, bare and waiting. Come closer. {e}",
    "Soft skin, hard nipples, and a very dirty mind tonight. {e}",
    "Fully naked and online. My body is yours to look at right now. {e}",
    "These curves aren't hiding anymore. Want a closer look? {e}",
    "Bare, wet, and ready for 1-on-1 attention. {e}",
    "I took everything off just for you. Don't be shy. {e}",
    "Nipples out, legs open, live and unfiltered. {e}",
    "No bra, no panties — just me and this cam. {e}",
    "Feeling extra naughty. My body is on full display. {e}",
    "Every inch of me is online right now. Come watch. {e}",
    "Hard nipples and a soft bed. Guess where I am. {e}",
    "Stripped down and live. Private shows start when you join. {e}",
    "I'm not wearing a single thing. Your move. {e}",
    "Body on show, mind in the gutter. Join me live. {e}",
    "These tits are out and ready for attention. {e}",
    "Ass up, cam on, waiting for someone fun. {e}",
    "Naked and bored until you show up. {e}",
    "Skin only. No filters. Real body, real time. {e}",
    "I undressed just so you could stare. Enjoy. {e}",
    "Live, nude, and in the mood. 1-on-1 is open. {e}",
    "My nipples got hard the second the cam went on. {e}",
    "Nothing left to the imagination — come see. {e}",
    "Bare skin and dirty thoughts. Private chat is open. {e}",
    "Fully exposed and loving every second of it. {e}",
]

_ACTION_LINE_TEMPLATES = [
    "Join my private show",
    "Watch me live now",
    "Start 1-on-1 chat",
    "Come play with me",
    "Enter private cam",
    "Unlock full access",
    "See me completely nude",
    "Join exclusive live",
    "Open private room",
    "Chat with me live",
    "Get the full show",
    "Watch every inch",
    "Private nude live",
    "Come inside now",
    "Live cam is open",
    "Tap for more of me",
    "See what I'm hiding",
    "Join my OnlyFans",
    "Full nude content here",
    "Don't miss this show",
]

_RICH_LINK_DISPLAY_OPTIONS = [
    "Live Models",
    "Live Cam",
    "1-on-1 Live",
    "Private Show",
    "Live Chat",
    "Join Live",
    "Watch Live",
    "Private Cam",
    "Adult Live",
    "Live Now",
    "OnlyFans",
    "Full Video",
]


def _pick_emoji():
    return random.choice(_CAPTION_EMOJIS)


def generate_body_caption():
    """Unique generated body caption with trailing emoji."""
    tmpl = random.choice(_BODY_CAPTION_TEMPLATES)
    return tmpl.format(e=_pick_emoji())


def generate_action_line():
    words = random.choice(_ACTION_LINE_TEMPLATES)
    return f"💖 {words} 😘"


def clean_sheet_caption(raw):
    """Normalise a caption taken from the sheet: drop URLs (links are added
    separately, never twice), map @mentions to this account, tidy whitespace
    but keep intentional line breaks."""
    if not raw:
        return ""
    text = str(raw).replace("\r\n", "\n").replace("\r", "\n")
    text = _URL_RE.sub("", text)
    text = replace_mentions(text)
    text = "\n".join(re.sub(r"[ \t]{2,}", " ", line).strip() for line in text.split("\n"))
    text = re.sub(r"\n{3,}", "\n\n", text).strip()
    return text


def resolve_body_caption(sheet_caption, allow_generated_fallback=True):
    """Decide the body caption for ONE post according to CAPTION_MODE.

    Returns (caption_text, source) where source is one of:
      "sheet"            – caption came from the PostPlan/LinkPlan row
      "custom"           – generated caption (chosen by mode)
      "custom-fallback"  – sheet caption was empty, generated one used instead
      "none"             – no caption (disabled, or empty sheet caption with
                           fallback turned off)
    """
    cfg = _cfg()
    if not cfg.get("caption_enabled", True):
        return "", "none"

    mode = cfg.get("caption_mode", "custom")
    if mode == "mixed":
        use_sheet = random.random() < cfg.get("caption_sheet_percentage", 0.5)
        mode = "sheet" if use_sheet else "custom"

    if mode == "custom":
        return generate_body_caption(), "custom"

    # mode == "sheet"
    text = clean_sheet_caption(sheet_caption)
    if text:
        return text, "sheet"
    if cfg.get("caption_fallback_custom", True) and allow_generated_fallback:
        return generate_body_caption(), "custom-fallback"
    return "", "none"


def choose_caption_and_link_style(sheet_caption, add_link):
    """Build the post pieces matching the desired layout.

    Returns:
      body_caption: str   — body text (sheet or generated, per CAPTION_MODE)
      caption_source: str — "sheet" | "custom" | "custom-fallback" | "none"
      action_line:  str   — "💖 action words 😘" (empty if no link)
      link_mode: None | "rich" | "plain"
      rich_display: str or None
    """
    cfg = _cfg()
    body_caption, caption_source = resolve_body_caption(sheet_caption)

    if not add_link:
        return body_caption, caption_source, "", None, None

    action_line = generate_action_line()

    style = (cfg.get("link_style") or "random").strip().lower()
    if style == "rich":
        link_mode = "rich"
    elif style == "plain":
        link_mode = "plain"
    else:
        link_mode = random.choice(["rich", "plain"])

    rich_display = None
    if link_mode == "rich":
        account_display = (cfg.get("link_display_text") or "").strip()
        bare_url = (cfg.get("link_url") or "").replace("https://", "").replace("http://", "").lower()
        only_custom = cfg.get("link_display_text_only", False)
        if only_custom:
            rich_display = account_display if account_display and account_display.lower() not in (bare_url, "") else "Live Models"
        else:
            if account_display and account_display.lower() not in (bare_url, ""):
                rich_display = account_display if random.random() < 0.55 else random.choice(_RICH_LINK_DISPLAY_OPTIONS)
            else:
                rich_display = random.choice(_RICH_LINK_DISPLAY_OPTIONS)

    return body_caption, caption_source, action_line, link_mode, rich_display


# ═══════════════════════════════════════════════════════════════════════════
#  LINK-IN-POST DECISION
# ═══════════════════════════════════════════════════════════════════════════

def should_add_link(kind):
    cfg     = _cfg()
    enabled = cfg["link_enabled_image"] if kind == "image" else cfg["link_enabled_video"]
    if not enabled:
        return False
    return random.random() < cfg["link_percentage"]


# ═══════════════════════════════════════════════════════════════════════════
#  POST-TYPE SELECTION
# ═══════════════════════════════════════════════════════════════════════════

def _today_utc_str():
    return time.strftime("%Y-%m-%d", time.gmtime())


def get_video_count_today():
    """Videos this account already posted today (UTC); resets on a new day."""
    cfg = _cfg()
    max_v = cfg.get("max_videos_per_day", 0)
    if max_v <= 0:
        return 0
    today = _today_utc_str()
    stored_date = (cfg.get("video_count_date") or "").strip()
    if stored_date != today:
        return 0
    try:
        return max(0, int(float(cfg.get("video_count_today") or "0")))
    except (ValueError, TypeError):
        return 0


def increment_video_count():
    global _account_config
    cfg = _cfg()
    max_v = cfg.get("max_videos_per_day", 0)
    if max_v <= 0:
        return
    today = _today_utc_str()
    current = get_video_count_today()
    new_count = current + 1

    core = load_core_data(force=True)
    header = hmap(core["creds"])
    count_col = header.get("VIDEO_COUNT_TODAY")
    date_col  = header.get("VIDEO_COUNT_DATE")
    if count_col is None or date_col is None:
        print("Warning: VIDEO_COUNT_TODAY / VIDEO_COUNT_DATE columns missing — cannot track video limit.")
        return
    excel_row = ACCOUNT_ROW + 1
    sheets_batch_update_values([
        {"range": qrange(CREDS_TAB, f"{col_letter(count_col)}{excel_row}"), "values": [[str(new_count)]]},
        {"range": qrange(CREDS_TAB, f"{col_letter(date_col)}{excel_row}"),  "values": [[today]]},
    ])
    if _account_config:
        _account_config["video_count_today"] = str(new_count)
        _account_config["video_count_date"]  = today
    print(f"Video count for today updated: {new_count}/{max_v}")


def choose_media_kind():
    """Pick image / video / previewLink by ratio; never 'video' once the
    daily video limit is hit."""
    cfg = _cfg()
    max_v = cfg.get("max_videos_per_day", 0)
    used  = get_video_count_today() if max_v > 0 else 0
    video_allowed = (max_v <= 0) or (used < max_v)

    kinds   = ["image", "video", "previewLink"]
    weights = [cfg["image_ratio"], cfg["video_ratio"], cfg["link_ratio"]]

    if not video_allowed:
        print(f"Video daily limit reached ({used}/{max_v}) — skipping video this cycle, "
              f"will post image or previewLink instead.")
        weights = [cfg["image_ratio"], 0.0, cfg["link_ratio"]]
        total = sum(weights)
        if total <= 0:
            return "image"
        weights = [w / total for w in weights]

    return random.choices(kinds, weights=weights, k=1)[0]


# ═══════════════════════════════════════════════════════════════════════════
#  POST-PLAN SHEET (File Name + Caption + Status)
# ═══════════════════════════════════════════════════════════════════════════

_post_plan_cache          = None
_post_plan_status_col_idx = None


def get_post_plan_tab_name():
    return _cfg()["post_plan_sheet_name"]


def load_post_plan(force_refresh=False):
    global _post_plan_cache, _post_plan_status_col_idx
    if _post_plan_cache is not None and not force_refresh:
        return _post_plan_cache

    tab_name = get_post_plan_tab_name()
    link_tab = get_link_plan_tab_name()
    plans = load_plan_data(tab_name, link_tab, force=force_refresh)
    values = plans["by_tab"].get(tab_name, [])

    if not values:
        print(f"Warning: post-plan sheet '{tab_name}' not found (or empty) in the spreadsheet — "
              f"add a tab with that name (File Name / Caption / Status columns).")
        _post_plan_cache = {}
        return _post_plan_cache

    header = hmap(values)

    def ci(*names):
        for n in names:
            if n.upper() in header:
                return header[n.upper()]
        return None

    file_idx    = ci("file name", "filename", "file")
    caption_idx = ci("caption", "captions")
    status_idx  = ci("status")
    _post_plan_status_col_idx = status_idx

    if file_idx is None:
        print(f"Warning: post-plan needs a 'File Name' column. Found: {list(header)}")
        _post_plan_cache = {}
        return _post_plan_cache
    if caption_idx is None:
        # Only a real problem if the sheet captions are actually wanted.
        if _cfg().get("caption_mode", "custom") in ("sheet", "mixed"):
            print("Warning: no 'Caption' column in post-plan — sheet captions will be empty "
                  "(generated fallback applies if enabled).")
        else:
            print("Note: no 'Caption' column in post-plan (fine — CAPTION_MODE=custom).")
    if status_idx is None:
        print("Warning: no 'Status' column — posted files won't be tracked.")

    plan_exact = {}
    plan_lower = {}
    already    = 0
    for excel_row in range(2, len(values) + 1):
        fname   = cell(values, excel_row, file_idx)
        caption = cell(values, excel_row, caption_idx) if caption_idx else ""
        status  = cell(values, excel_row, status_idx) if status_idx else ""
        if not fname:
            continue
        entry = {"caption": caption, "row": excel_row, "status": status}
        plan_exact[fname]         = entry
        plan_lower[fname.lower()] = entry
        if status.lower() == POSTED_STATUS_VALUE:
            already += 1

    print(f"Loaded {len(plan_exact)} post-plan rows ({already} already posted).")
    _post_plan_cache = {"exact": plan_exact, "lower": plan_lower}
    return _post_plan_cache


def find_plan_entry(plan, filename):
    exact = plan.get("exact", {})
    lower = plan.get("lower", {})
    return (
        exact.get(filename)
        or lower.get(filename.lower())
        or lower.get(os.path.splitext(filename.lower())[0])
    )


def mark_posted(filename, row_number, retries=3):
    global _post_plan_cache
    if _post_plan_status_col_idx is None:
        print(f"Warning: no 'Status' column — cannot mark '{filename}' as posted.")
        return

    tab_name = get_post_plan_tab_name()
    rng = qrange(tab_name, f"{col_letter(_post_plan_status_col_idx)}{row_number}")

    for attempt in range(1, retries + 1):
        try:
            sheets_update(rng, [[POSTED_STATUS_VALUE]])
            if _post_plan_cache:
                for d in (_post_plan_cache.get("exact", {}), _post_plan_cache.get("lower", {})):
                    for entry in d.values():
                        if entry["row"] == row_number:
                            entry["status"] = POSTED_STATUS_VALUE
            print(f"Marked '{filename}' row {row_number} as posted.")
            return
        except Exception as exc:
            if attempt < retries:
                wait = 2 ** attempt
                print(f"  mark_posted attempt {attempt}/{retries} failed ({exc}); retrying in {wait}s…")
                time.sleep(wait)
            else:
                print(f"ERROR: could not mark '{filename}' as posted after {retries} attempts: {exc}")
                print("  Post was successful — file will be moved. Row may need manual update.")


# ═══════════════════════════════════════════════════════════════════════════
#  LINKPLAN SHEET (URL + Caption + Status)
# ═══════════════════════════════════════════════════════════════════════════

def get_link_plan_tab_name():
    return _cfg()["link_plan_sheet_name"]


def load_link_plan(force_refresh=False):
    tab_name  = get_link_plan_tab_name()
    post_tab  = get_post_plan_tab_name()
    plans = load_plan_data(post_tab, tab_name, force=force_refresh)
    values = plans["by_tab"].get(tab_name, [])
    if not values:
        return []

    header = hmap(values)

    def ci(*names):
        for n in names:
            if n.upper() in header:
                return header[n.upper()]
        return None

    url_idx    = ci("url")
    cap_idx    = ci("caption", "captions")
    status_idx = ci("status")
    if url_idx is None:
        raise RuntimeError(f"'{tab_name}' needs a 'URL' column.")

    out = []
    for excel_row in range(2, len(values) + 1):
        url = cell(values, excel_row, url_idx)
        if not url:
            continue
        caption = cell(values, excel_row, cap_idx) if cap_idx else ""
        status  = cell(values, excel_row, status_idx) if status_idx else ""
        out.append({
            "url": url, "caption": caption, "status": status,
            "row": excel_row, "status_col": status_idx,
        })
    return out


def pick_next_url():
    plan = load_link_plan()
    for entry in plan:
        s = entry["status"].lower()
        if s == POSTED_STATUS_VALUE or s.startswith(CLAIM_PREFIX.lower()):
            continue
        return entry
    return None


def claim_url_row(entry):
    """Optimistic claim: re-read the cell, then write."""
    if entry["status_col"] is None:
        return True
    tab_name  = get_link_plan_tab_name()
    rng       = qrange(tab_name, f"{col_letter(entry['status_col'])}{entry['row']}")
    claim_val = f"{CLAIM_PREFIX}{RUN_TAG}"

    fresh = sheets_get(rng)
    current_rows = fresh.get("values", [])
    current = str(current_rows[0][0]).strip() if current_rows and current_rows[0] else ""
    if current.lower() == POSTED_STATUS_VALUE or current.lower().startswith(CLAIM_PREFIX.lower()):
        return False

    sheets_update(rng, [[claim_val]])
    return True


def mark_url_posted(entry):
    if entry["status_col"] is None:
        return
    tab_name = get_link_plan_tab_name()
    rng = qrange(tab_name, f"{col_letter(entry['status_col'])}{entry['row']}")
    sheets_update(rng, [[POSTED_STATUS_VALUE]])


def release_url_claim(entry):
    if entry["status_col"] is None:
        return
    tab_name = get_link_plan_tab_name()
    rng = qrange(tab_name, f"{col_letter(entry['status_col'])}{entry['row']}")
    try:
        sheets_update(rng, [[""]])
    except Exception as exc:
        print(f"Warning: could not release claim on LinkPlan row {entry['row']}: {exc}")


# ═══════════════════════════════════════════════════════════════════════════
#  LINK PREVIEW
# ═══════════════════════════════════════════════════════════════════════════

def fetch_link_metadata(url, timeout=20):
    last_exc = None
    for attempt in range(1, LINK_PREVIEW_MAX_RETRIES + 1):
        try:
            resp = requests.get(
                CARDYB_EXTRACT_URL,
                params={"url": url},
                headers=REQUEST_HEADERS,
                timeout=timeout,
            )
            resp.raise_for_status()
            data = resp.json()
            return {
                "title": (data.get("title") or url)[:300],
                "description": (data.get("description") or "")[:1000],
                "image": data.get("image") or None,
                "final_url": url,
            }
        except (requests.exceptions.RequestException, ValueError) as exc:
            last_exc = exc
            print(f"Attempt {attempt}/{LINK_PREVIEW_MAX_RETRIES} to fetch via cardyb failed: {exc}")
            if attempt < LINK_PREVIEW_MAX_RETRIES:
                delay = LINK_PREVIEW_RETRY_DELAY * (2 ** (attempt - 1))
                print(f"Retrying in {delay}s…")
                time.sleep(delay)

    print(f"cardyb extraction failed after {LINK_PREVIEW_MAX_RETRIES} attempts ({last_exc}); "
          f"falling back to manual scrape.")
    return _fetch_link_metadata_manual(url, timeout)


def _fetch_link_metadata_manual(url, timeout=20):
    last_exc = None
    for attempt in range(1, LINK_PREVIEW_MAX_RETRIES + 1):
        try:
            resp = requests.get(url, headers=REQUEST_HEADERS, timeout=timeout, allow_redirects=True)
            resp.raise_for_status()
            return _parse_link_metadata(resp)
        except requests.exceptions.RequestException as exc:
            last_exc = exc
            print(f"Attempt {attempt}/{LINK_PREVIEW_MAX_RETRIES} to manually fetch {url} failed: {exc}")
            if attempt < LINK_PREVIEW_MAX_RETRIES:
                delay = LINK_PREVIEW_RETRY_DELAY * (2 ** (attempt - 1))
                print(f"Retrying in {delay}s…")
                time.sleep(delay)

    raise NoPreviewError(
        f"Failed to fetch {url} after {LINK_PREVIEW_MAX_RETRIES} attempts (cardyb + manual)"
    ) from last_exc


def _parse_link_metadata(resp):
    soup = BeautifulSoup(resp.text, "html.parser")
    final_url = resp.url

    def meta(*props):
        for prop in props:
            tag = soup.find("meta", property=prop) or soup.find("meta", attrs={"name": prop})
            if tag and tag.get("content"):
                return tag["content"].strip()
        return None

    title = meta("og:title", "twitter:title") or (
        soup.title.string.strip() if soup.title and soup.title.string else resp.url
    )
    description = meta("og:description", "twitter:description", "description") or ""
    raw_image = meta("og:image", "og:image:url", "twitter:image")
    image = urljoin(final_url, raw_image) if raw_image else None

    return {"title": title[:300], "description": description[:1000], "image": image, "final_url": final_url}


def upload_link_thumbnail(client, image_url, referer, max_bytes, timeout=20):
    if not image_url:
        print("No preview image found — posting without a thumbnail.")
        return None

    headers = {**REQUEST_HEADERS, "Referer": referer}
    last_exc = None
    for attempt in range(1, LINK_PREVIEW_MAX_RETRIES + 1):
        try:
            img_resp = requests.get(image_url, headers=headers, timeout=timeout)
            img_resp.raise_for_status()
            content_type = img_resp.headers.get("Content-Type", "")
            if "image" not in content_type:
                print(f"Warning: fetched image URL did not return an image (Content-Type: {content_type!r})")
                return None

            data = img_resp.content
            if len(data) > max_bytes:
                data = _compress_link_thumb(data, max_bytes)
                if data is None:
                    return None

            upload = client.upload_blob(data)
            return upload.blob
        except Exception as exc:  # noqa: BLE001
            last_exc = exc
            print(f"Attempt {attempt}/{LINK_PREVIEW_MAX_RETRIES} to fetch/upload thumbnail failed: {exc}")
            if attempt < LINK_PREVIEW_MAX_RETRIES:
                delay = LINK_PREVIEW_RETRY_DELAY * (2 ** (attempt - 1))
                print(f"Retrying in {delay}s…")
                time.sleep(delay)

    print(f"Warning: thumbnail could not be fetched/uploaded after all retries ({last_exc}); posting without one.")
    return None


def _compress_link_thumb(data, max_bytes):
    try:
        from PIL import Image
        img = Image.open(io.BytesIO(data))
        if img.mode in ("RGBA", "P", "LA"):
            img = img.convert("RGB")
        for q in range(85, 20, -10):
            buf = io.BytesIO()
            img.save(buf, format="JPEG", quality=q, optimize=True)
            if buf.tell() <= max_bytes:
                return buf.getvalue()
        return buf.getvalue()
    except Exception as exc:
        print(f"Warning: could not compress thumbnail: {exc}")
        return None


MAX_POST_GRAPHEMES = 300
SAFETY_MARGIN = 5


def grapheme_len(s: str) -> int:
    """Unicode grapheme cluster count (what Bluesky actually enforces)."""
    return grapheme.length(s)


def _trim_to_budget(text, budget):
    """Trim `text` (with a trailing ellipsis) so it fits `budget` graphemes."""
    if budget <= 0 or not text:
        return ""
    if grapheme_len(text) <= budget:
        return text
    lo, hi, best = 0, len(text), ""
    while lo <= hi:
        mid = (lo + hi) // 2
        trial = text[:mid].rstrip()
        if mid < len(text):
            trial += "…"
        if grapheme_len(trial) <= budget:
            best = trial
            lo = mid + 1
        else:
            hi = mid - 1
    return best


def build_link_caption_text(caption, tags, fallback_url=None):
    text = _URL_RE.sub("", caption or "").strip(" \t\r")
    if fallback_url:
        text = f"{text}\n{fallback_url}".strip(" \t\r") if text else fallback_url

    def _make(t):
        tb = TextBuilder()
        if t:
            tb.text(t)
        if tags:
            if t:
                tb.text("\n\n")
            for i, tag in enumerate(tags):
                tb.tag(f"#{tag}", tag)
                if i < len(tags) - 1:
                    tb.text(" ")
        return tb

    tb = _make(text)
    limit = MAX_POST_GRAPHEMES - SAFETY_MARGIN
    if grapheme_len(tb.build_text()) > limit:
        hashtag_block = ("\n\n" + " ".join(f"#{t}" for t in tags)) if tags else ""
        budget = limit - grapheme_len(hashtag_block)
        tb = _make(_trim_to_budget(text, budget))
    return tb


def build_external_embed(client, preview, max_thumb_bytes, timeout):
    thumb_blob = upload_link_thumbnail(
        client, preview["image"], referer=preview["final_url"],
        max_bytes=max_thumb_bytes, timeout=timeout,
    )
    return models.AppBskyEmbedExternal.Main(
        external=models.AppBskyEmbedExternal.External(
            uri=preview["final_url"],
            title=preview["title"],
            description=preview["description"],
            thumb=thumb_blob,
        )
    )


def compose_fallback_caption(preview):
    if not preview:
        return ""
    title = (preview.get("title") or "").strip()
    description = (preview.get("description") or "").strip()
    parts = [p for p in (title, description) if p]
    if not parts:
        return ""
    return "\n" + "\n".join(parts)


def post_link_card(client, url, caption, tags, timeout, max_thumb_bytes, auto_caption_enabled=True):
    """previewLink post. Caption follows CAPTION_MODE (sheet / custom / mixed).
    AUTO_CAPTION_ENABLED_LINK only governs the generated *fallback* used when
    the sheet caption is empty."""
    print(f"[previewLink] Fetching preview for: {url}")
    preview = None
    embed = None
    try:
        preview = fetch_link_metadata(url, timeout)
        print(f"  title: {preview['title']!r}")
        embed = build_external_embed(client, preview, max_thumb_bytes, timeout)
    except Exception as exc:
        print(f"Warning: preview fetch failed ({exc}); posting as plain link instead.")

    effective_caption, caption_source = resolve_body_caption(
        caption, allow_generated_fallback=auto_caption_enabled
    )
    if caption_source == "none":
        print("No caption used for this previewLink post "
              "(disabled, or empty sheet caption with fallback/auto-caption off).")
    else:
        print(f"previewLink caption source: {caption_source} → {effective_caption!r}")

    # The embed already carries the destination URL, so no extra link in text.
    tb = build_link_caption_text(effective_caption, tags, fallback_url=(url if preview is None else None))
    client.send_post(text=tb, embed=embed)

    posted_url = preview["final_url"] if preview else url
    print(f"✓ Posted {'link card' if embed else 'plain link'} for {posted_url} "
          f"(caption={caption_source}, tags={len(tags)})")


# ═══════════════════════════════════════════════════════════════════════════
#  MEGA.NZ HELPERS (via rclone) — image/video media
# ═══════════════════════════════════════════════════════════════════════════

_IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".tiff", ".avif", ".heic"}
_VIDEO_EXTS = {".mp4", ".mov", ".avi", ".mkv", ".webm", ".m4v", ".flv", ".wmv", ".3gp", ".ts"}


def _kind_from_filename(filename):
    ext = os.path.splitext(filename.lower())[1]
    if ext in _IMAGE_EXTS:
        return "image"
    if ext in _VIDEO_EXTS:
        return "video"
    return None


# Files that failed to post twice in this process are skipped so one bad file
# can't block the whole queue forever.
_BAD_MEDIA = {}


def fetch_media_matching_plan(preferred_kind, plan):
    cfg           = _cfg()
    upload_folder = cfg["mega_upload_folder"]
    if not upload_folder:
        raise RuntimeError("MEGA_UPLOAD_FOLDER is empty in credentials sheet.")

    remote_folder = f"{RCLONE_REMOTE_NAME}:{upload_folder}"
    files = rclone_list_files(remote_folder)
    candidates = [f for f in files if not f.startswith(CLAIM_PREFIX)
                  and _kind_from_filename(f) == preferred_kind
                  and _BAD_MEDIA.get(f, 0) < 2]

    counters = {"claim": 0, "plan": 0, "posted": 0}

    for name in candidates:
        entry = find_plan_entry(plan, name)
        if entry is None:
            counters["plan"] += 1
            continue
        if entry["status"].lower() == POSTED_STATUS_VALUE:
            counters["posted"] += 1
            continue

        print(f"Found {preferred_kind}: '{name}'")
        claimed_name = rclone_claim(remote_folder, name)
        if claimed_name is None:
            counters["claim"] += 1
            continue
        print(f"Claimed as '{claimed_name}'.")

        local_path = f"/tmp/{name}"
        if not rclone_download(remote_folder, claimed_name, local_path):
            print(f"Warning: download failed for claimed file '{claimed_name}' — releasing claim.")
            rclone_move(f"{remote_folder}/{claimed_name}", f"{remote_folder}/{name}")
            continue

        file_info = {"original_name": name, "claimed_name": claimed_name}
        return file_info, local_path, preferred_kind, entry["caption"], entry["row"]

    print(f"No {preferred_kind} match: "
          f"{counters['plan']} not in plan, {counters['posted']} already posted, "
          f"{counters['claim']} claimed by another run.")
    return None, None, None, None, None


# ── MP4 / QuickTime handling ───────────────────────────────────────────────
# Bluesky only accepts video/mp4. The server decides the type by SNIFFING the
# file bytes (not the extension): a MOV/QuickTime file named ".mp4" is rejected
# with  Expected "video/mp4" (got "video/quicktime").
# We therefore (1) read the real container brand ourselves in pure Python,
# (2) only convert when needed, (3) get an ffmpeg binary even if the runner
# doesn't have one, and (4) verify the result before posting.

_FFMPEG_BIN = None
_FFMPEG_TRIED = False


def _get_ffmpeg():
    """Return a usable ffmpeg executable path, or None.
    Order: system ffmpeg -> pip 'imageio-ffmpeg' (bundled static binary, no
    root needed) -> sudo apt-get install ffmpeg. Result cached per process."""
    global _FFMPEG_BIN, _FFMPEG_TRIED
    if _FFMPEG_TRIED:
        return _FFMPEG_BIN
    _FFMPEG_TRIED = True

    import shutil
    found = shutil.which("ffmpeg")
    if found:
        _FFMPEG_BIN = found
        return _FFMPEG_BIN

    print("ffmpeg not found on this runner — trying pip install imageio-ffmpeg …")
    try:
        subprocess.run([sys.executable, "-m", "pip", "install", "-q",
                        "--break-system-packages", "imageio-ffmpeg"],
                       capture_output=True, text=True, timeout=300)
        import imageio_ffmpeg
        exe = imageio_ffmpeg.get_ffmpeg_exe()
        if exe and os.path.exists(exe):
            _FFMPEG_BIN = exe
            print(f"Using bundled ffmpeg: {exe}")
            return _FFMPEG_BIN
    except Exception as exc:
        print(f"Warning: imageio-ffmpeg install failed: {exc}")

    print("Trying apt-get install ffmpeg …")
    try:
        subprocess.run(["sudo", "-n", "apt-get", "install", "-y", "-qq", "ffmpeg"],
                       capture_output=True, text=True, timeout=600)
        found = shutil.which("ffmpeg")
        if found:
            _FFMPEG_BIN = found
            return _FFMPEG_BIN
    except Exception as exc:
        print(f"Warning: apt-get ffmpeg install failed: {exc}")

    print("ERROR: no ffmpeg available — will use the pure-Python brand patch as a last resort.")
    return None


def _read_brand(path):
    """Container major brand read straight from the file bytes.
    Returns e.g. 'isom', 'mp42', 'qt  ', or None if the file does not start
    with an 'ftyp' box (old-style MOV with moov/mdat/free first — the server
    also sniffs those as QuickTime)."""
    try:
        with open(path, "rb") as f:
            head = f.read(16)
        if len(head) >= 12 and head[4:8] == b"ftyp":
            return head[8:12].decode("latin-1")
    except Exception:
        pass
    return None


def _brand_ok(brand):
    return brand is not None and not brand.lower().startswith("qt")


def _patch_brand_in_place(src, dst):
    """Last resort without ffmpeg: copy the file and rewrite the ftyp major
    brand 'qt  ' -> 'mp42' so the server sniffs it as MP4. Only possible when
    the file already starts with an ftyp box."""
    if _read_brand(src) is None:
        return False
    import shutil
    shutil.copyfile(src, dst)
    with open(dst, "r+b") as f:
        f.seek(8)
        f.write(b"mp42")
    return _brand_ok(_read_brand(dst))


def ensure_real_mp4(local_path, force_reencode=False):
    """Make sure `local_path` is a genuine MP4 that Bluesky will accept.
    Returns the path to post (a new *_fixed.mp4 file if conversion happened)."""
    brand = _read_brand(local_path)
    print(f"Video container brand: {brand!r}")

    if _brand_ok(brand) and not force_reencode:
        print("Video is already a proper MP4 — no conversion needed.")
        return local_path

    base = os.path.splitext(local_path)[0]
    out  = f"{base}_fixed.mp4"
    ffmpeg = _get_ffmpeg()

    def _cleanup_out():
        if os.path.exists(out):
            try:
                os.remove(out)
            except OSError:
                pass

    if ffmpeg:
        common_in  = [ffmpeg, "-y", "-v", "error", "-i", local_path,
                      "-map", "0:v:0", "-map", "0:a:0?", "-sn", "-dn", "-map_metadata", "-1"]
        common_out = ["-movflags", "+faststart", "-brand", "mp42", "-f", "mp4", out]
        attempts = []
        if not force_reencode:
            attempts.append(("stream-copy", common_in + ["-c", "copy"] + common_out))
        attempts.append(("re-encode", common_in + [
            "-c:v", "libx264", "-preset", "veryfast", "-crf", "23", "-pix_fmt", "yuv420p",
            "-c:a", "aac", "-b:a", "128k", "-ac", "2"] + common_out))

        for label, cmd in attempts:
            _cleanup_out()
            try:
                r = subprocess.run(cmd, capture_output=True, text=True, timeout=900)
            except Exception as exc:
                print(f"Warning: ffmpeg {label} could not run: {exc}")
                continue
            if r.returncode != 0 or not os.path.exists(out) or os.path.getsize(out) == 0:
                print(f"Warning: ffmpeg {label} failed: {(r.stderr or '').strip()[-300:]}")
                continue
            new_brand = _read_brand(out)
            if not _brand_ok(new_brand):
                print(f"Warning: {label} output still not a proper MP4 (brand {new_brand!r}).")
                continue
            print(f"Video fixed via {label}: {brand!r} → {new_brand!r}, "
                  f"{os.path.getsize(out)/(1024*1024):.1f} MB.")
            try:
                os.remove(local_path)
            except OSError:
                pass
            return out
        _cleanup_out()

    # Last resort (no ffmpeg, or ffmpeg failed): patch the brand bytes.
    try:
        if _patch_brand_in_place(local_path, out):
            print(f"Video fixed via brand patch (no re-encode): {brand!r} → {_read_brand(out)!r}.")
            try:
                os.remove(local_path)
            except OSError:
                pass
            return out
    except Exception as exc:
        print(f"Warning: brand patch failed: {exc}")
    _cleanup_out()

    print("WARNING: could not convert this video to a proper MP4 — posting original; "
          "Bluesky will probably reject it.")
    return local_path


def compress_image_under_limit(local_path):
    from PIL import Image
    max_bytes = _cfg()["max_image_bytes"]
    orig = os.path.getsize(local_path)
    if orig <= max_bytes:
        print(f"Image {orig/1024:.0f} KB — no compression needed.")
        return local_path
    img = Image.open(local_path)
    if img.mode in ("RGBA", "P", "LA"):
        img = img.convert("RGB")
    for q in range(90, 20, -10):
        buf = io.BytesIO()
        img.save(buf, format="JPEG", quality=q, optimize=True)
        if buf.tell() <= max_bytes:
            with open(local_path, "wb") as f:
                f.write(buf.getvalue())
            print(f"Compressed {orig/1024:.0f} KB → {buf.tell()/1024:.0f} KB (q={q}).")
            return local_path
    w, h = img.size
    scale = 0.9
    while scale > 0.3:
        r = img.resize((max(1, int(w * scale)), max(1, int(h * scale))), Image.LANCZOS)
        buf = io.BytesIO()
        r.save(buf, format="JPEG", quality=70, optimize=True)
        if buf.tell() <= max_bytes:
            with open(local_path, "wb") as f:
                f.write(buf.getvalue())
            print(f"Resized+compressed → {buf.tell()/1024:.0f} KB.")
            return local_path
        scale -= 0.1
    with open(local_path, "wb") as f:
        f.write(buf.getvalue())
    print(f"Warning: best-effort compression = {buf.tell()/1024:.0f} KB.")
    return local_path


def move_file_to_processed(claimed_name, original_name):
    cfg = _cfg()
    remote_upload    = f"{RCLONE_REMOTE_NAME}:{cfg['mega_upload_folder']}"
    remote_processed = f"{RCLONE_REMOTE_NAME}:{cfg['mega_processed_folder']}"
    ok = rclone_move(f"{remote_upload}/{claimed_name}", f"{remote_processed}/{original_name}")
    print("Moved to processed folder on Mega." if ok else
          "Warning: failed to move file to processed folder on Mega — check manually.")
    return ok


def release_claim(claimed_name, original_name):
    cfg = _cfg()
    remote_upload = f"{RCLONE_REMOTE_NAME}:{cfg['mega_upload_folder']}"
    ok = rclone_move(f"{remote_upload}/{claimed_name}", f"{remote_upload}/{original_name}")
    print(f"Released claim on '{original_name}'." if ok else
          f"Warning: could not release claim for '{original_name}'.")
    return ok


# ═══════════════════════════════════════════════════════════════════════════
#  IMAGE/VIDEO POST BUILDING
# ═══════════════════════════════════════════════════════════════════════════

def build_post_from_caption(body_caption, action_line, tags, link_mode=None, rich_display=None):
    """
    Priority when the post is too long:
      1. Keep full body caption (highest priority)
      2. Keep as many hashtags as possible
      3. Drop action line + link if still needed
      4. Only as last resort → trim body caption
    Works the same for sheet-inherited and generated captions.
    """
    cfg = _cfg()
    # body_caption is already cleaned (URLs removed, mentions mapped) by
    # resolve_body_caption(); this is a harmless second pass for safety.
    text = _URL_RE.sub("", body_caption).strip() if body_caption else ""
    tags = tags or []

    on_new_line = cfg.get("link_on_new_line", True)

    def _assemble(caption_text, use_action=True, tag_list=None):
        tb = TextBuilder()
        if caption_text:
            tb.text(caption_text)

        if link_mode in ("rich", "plain") and use_action:
            if caption_text:
                tb.text("\n\n" if on_new_line else " ")
            if action_line:
                tb.text(action_line + " ")
            url = cfg["link_url"]
            if link_mode == "rich":
                display = (rich_display or cfg.get("link_display_text") or "Live Models").strip()
                tb.link(display, url)
            else:
                tb.link(url, url)

        if tag_list:
            if caption_text or (link_mode in ("rich", "plain") and use_action):
                tb.text("\n\n")
            for i, tag in enumerate(tag_list):
                tb.tag(f"#{tag}", tag)
                if i < len(tag_list) - 1:
                    tb.text(" ")
        return tb

    limit = MAX_POST_GRAPHEMES - SAFETY_MARGIN

    def _fits(caption_text, use_action, tag_list):
        return grapheme_len(_assemble(caption_text, use_action, tag_list).build_text()) <= limit

    def _max_tags(use_action):
        lo, hi, best_n = 0, len(tags), 0
        while lo <= hi:
            mid = (lo + hi) // 2
            if _fits(text, use_action, tags[:mid]):
                best_n = mid
                lo = mid + 1
            else:
                hi = mid - 1
        return best_n

    # 1. Full version
    if _fits(text, True, tags):
        return _assemble(text, True, tags)

    # 2. Full caption + action/link, fewer hashtags
    if tags:
        n = _max_tags(True)
        if n > 0:
            print(f"Caption too long → kept {n}/{len(tags)} hashtags to fit limit.")
            return _assemble(text, True, tags[:n])

    # 2b. Full caption + action/link, no hashtags
    if _fits(text, True, []):
        print("Caption too long → dropped all hashtags (kept action line + link).")
        return _assemble(text, True, [])

    # 3. Drop action line + link, keep as many hashtags as possible
    if tags:
        n = _max_tags(False)
        if n > 0:
            print(f"Caption too long → dropped action line, kept {n}/{len(tags)} hashtags.")
            return _assemble(text, False, tags[:n])

    # 4. No hashtags + no action line
    if _fits(text, False, []):
        print("Caption too long → dropped action line and all hashtags.")
        return _assemble(text, False, [])

    # 5. Last resort: trim body caption
    print(f"Caption still too long even after dropping hashtags/action "
          f"({grapheme_len(_assemble(text, False, []).build_text())} graphemes). Trimming body caption…")
    lo, hi, best_text = 0, len(text), ""
    while lo <= hi:
        mid = (lo + hi) // 2
        trial = text[:mid].rstrip()
        if mid < len(text):
            trial += "…"
        if _fits(trial, False, []):
            best_text = trial
            lo = mid + 1
        else:
            hi = mid - 1
    return _assemble(best_text, False, [])


def post_to_bluesky(client, media_name, local_path, kind, caption, tags, add_link):
    body_caption, caption_source, action_line, link_mode, rich_display = \
        choose_caption_and_link_style(caption, add_link)
    tb = build_post_from_caption(
        body_caption, action_line, tags,
        link_mode=link_mode, rich_display=rich_display,
    )
    if kind == "video":
        try:
            with open(local_path, "rb") as f:
                client.send_video(text=tb, video=f.read(), video_alt=media_name)
        except Exception as exc:
            msg = str(exc)
            if "video/quicktime" in msg or 'Expected "video/mp4"' in msg:
                # Server still sniffed the upload as QuickTime. Force a full
                # re-encode to a clean H.264/AAC MP4 and retry once.
                print("Server rejected video as QuickTime — forcing full re-encode and retrying once…")
                local_path = ensure_real_mp4(local_path, force_reencode=True)
                with open(local_path, "rb") as f:
                    client.send_video(text=tb, video=f.read(), video_alt=media_name)
            else:
                raise
    else:
        with open(local_path, "rb") as f:
            client.send_image(text=tb, image=f.read(), image_alt=media_name)

    link_info = "no"
    if link_mode == "rich":
        link_info = f"rich[{rich_display}]"
    elif link_mode == "plain":
        link_info = "plain-url"
    print(f"✓ Posted {kind} (caption source: {caption_source}): {body_caption!r}")
    if action_line:
        print(f"  Action: {action_line} → {link_info}")
    if tags:
        print(f"  Tags: {' '.join('#'+t for t in tags)}")
    return local_path   # may differ from the input if the video was re-encoded


# ═══════════════════════════════════════════════════════════════════════════
#  DISCOVER MODE
# ═══════════════════════════════════════════════════════════════════════════

def _claim_row_writes(excel_row, repo_col, astatus_col, at_col):
    now = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    data = []
    if repo_col is not None:
        data.append({"range": qrange(CREDS_TAB, f"{col_letter(repo_col)}{excel_row}"),
                     "values": [[CURRENT_REPO]]})
    if astatus_col is not None:
        data.append({"range": qrange(CREDS_TAB, f"{col_letter(astatus_col)}{excel_row}"),
                     "values": [[ASSIGN_STATUS_IN_USE]]})
    if at_col is not None:
        data.append({"range": qrange(CREDS_TAB, f"{col_letter(at_col)}{excel_row}"),
                     "values": [[now]]})
    if data:
        sheets_batch_update_values(data)


def run_discover():
    """Discover which account rows THIS repo should run (sticky assignment,
    capped by MAX_ACCOUNTS_PER_RUN, never touching rows owned by other repos)."""
    ensure_required_tabs()
    ensure_extra_columns(CREDS_TAB, [
        "ASSIGNED_REPO", "ASSIGNED_STATUS", "ASSIGNED_AT",
        "VIDEO_COUNT_TODAY", "VIDEO_COUNT_DATE",
    ])

    core = load_core_data(force=True)
    creds_values = core["creds"]
    if not creds_values:
        print(f"::error::'{CREDS_TAB}' tab not found or empty in the spreadsheet.")
        sys.exit(1)
    header = hmap(creds_values)

    def hidx(*names):
        for n in names:
            if n.upper() in header:
                return header[n.upper()]
        return None

    handle_col = hidx("BSKY_HANDLE")
    status_col = hidx("ACCOUNT_STATUS")
    repo_col   = hidx("ASSIGNED_REPO")
    astatus_col = hidx("ASSIGNED_STATUS")
    at_col     = hidx("ASSIGNED_AT")

    if handle_col is None:
        print(f"::error::'{CREDS_TAB}' needs a 'BSKY_HANDLE' column.")
        sys.exit(1)

    force_row = get_env("FORCE_ACCOUNT_ROW", required=False)
    if force_row:
        try:
            eligible = [max(1, int(force_row))]
        except ValueError:
            print(f"::error::FORCE_ACCOUNT_ROW={force_row!r} is not a valid row number.")
            sys.exit(1)
        print(f"FORCE_ACCOUNT_ROW set — running only row {eligible[0]} "
              f"(eligibility filter, assignment lock and MAX_ACCOUNTS_PER_RUN cap skipped).")
    else:
        owned = []
        free  = []

        for excel_row in range(2, len(creds_values) + 1):
            handle = cell(creds_values, excel_row, handle_col)
            if not handle:
                continue
            acct_status = cell(creds_values, excel_row, status_col).lower() if status_col else ""
            if any(marker in acct_status for marker in SKIP_STATUS_MARKERS):
                print(f"Skipping row {excel_row - 1} ({handle}) — status: {acct_status!r}")
                continue

            assigned_repo = cell(creds_values, excel_row, repo_col) if repo_col else ""
            assigned_status = cell(creds_values, excel_row, astatus_col) if astatus_col else ""

            data_idx = excel_row - 1
            if assigned_repo == CURRENT_REPO:
                owned.append(data_idx)
                print(f"  Owned by us: row {data_idx} ({handle})")
            elif assigned_repo and assigned_status.lower() == ASSIGN_STATUS_IN_USE.lower():
                print(f"  Locked by other repo '{assigned_repo}': row {data_idx} ({handle}) — skipped")
            else:
                free.append((data_idx, excel_row, handle))

        limit_raw = get_env("MAX_ACCOUNTS_PER_RUN", required=False)
        if not limit_raw:
            limit_raw = core["settings"].get("MAX_ACCOUNTS_PER_RUN", "")

        limit = None
        if limit_raw:
            try:
                limit = max(1, int(limit_raw))
            except ValueError:
                print(f"Warning: MAX_ACCOUNTS_PER_RUN={limit_raw!r} is not a valid number — no hard cap.")

        if limit is not None:
            print(f"MAX_ACCOUNTS_PER_RUN={limit} — this repo may run at most {limit} account(s).")
            if len(owned) > limit:
                print(f"Note: this repo already owns {len(owned)} accounts (more than the current "
                      f"limit of {limit}). Continuing with all owned accounts; no new claims.")
            else:
                slots_left = limit - len(owned)
                for data_idx, excel_row, handle in free[:slots_left]:
                    _claim_row_writes(excel_row, repo_col, astatus_col, at_col)
                    print(f"  Claimed free row {data_idx} ({handle}) for repo '{CURRENT_REPO}'.")
                    owned.append(data_idx)
            eligible = owned
        else:
            for data_idx, excel_row, handle in free:
                _claim_row_writes(excel_row, repo_col, astatus_col, at_col)
                print(f"  Claimed free row {data_idx} ({handle}) for repo '{CURRENT_REPO}'.")
                owned.append(data_idx)
            eligible = owned

        if not eligible:
            print(f"::error::No eligible account rows for repo '{CURRENT_REPO}' in '{CREDS_TAB}'. "
                  f"Either all accounts are banned/suspended, or they are already locked by "
                  f"other repositories and this repo has none of its own.")
            sys.exit(1)

    print(f"Account rows for this workflow run (repo={CURRENT_REPO}): {eligible}")
    rows_csv = ",".join(str(r) for r in eligible)

    gh_output = os.environ.get("GITHUB_OUTPUT")
    if not gh_output:
        raise RuntimeError("GITHUB_OUTPUT is not set — must be run inside a GitHub Actions step.")
    with open(gh_output, "a") as f:
        f.write(f"rows={rows_csv}\n")
        f.write(f"count={len(eligible)}\n")


# ═══════════════════════════════════════════════════════════════════════════
#  MAIN CYCLE
# ═══════════════════════════════════════════════════════════════════════════

def run_once():
    # Drop per-cycle plan caches so edits to captions/status in the sheet
    # (e.g. switching CAPTION_MODE or editing a Caption cell) take effect.
    global _plan_cache, _post_plan_cache
    _plan_cache = None
    _post_plan_cache = None

    cfg = refresh_account_config()

    if not try_acquire_account_lock():
        raise AccountLockedElsewhereError(
            f"Account row {ACCOUNT_ROW} is locked by another repo right now."
        )

    handle = cfg["handle"]

    proxy_url = ensure_account_proxy(cfg)
    cfg = _cfg()

    print_target_account(handle)
    try:
        client = build_bsky_client(proxy_url)
    except ProxyClientBuildError as exc:
        raise NoProxyAvailableError(str(exc)) from exc

    try:
        client.login(handle, cfg["app_pw"])
    except Exception as exc:
        err = str(exc)
        if proxy_url and _looks_like_proxy_error(exc):
            ip, port = cfg.get("proxy_ip", ""), cfg.get("proxy_port", "")
            if ip and port:
                release_or_kill_proxy(ip, port, alive=False)
                _clear_account_proxy()
            print(f"Login failed through proxy {proxy_url} — marked dead; "
                  f"a new proxy will be picked next cycle: {exc}")
            raise
        if "AccountTakedown" in err or "AccountSuspended" in err:
            raise AccountTakenDownError(f"Account {handle} taken down/suspended.") from exc
        if "AuthenticationRequired" in err or "Invalid identifier or password" in err:
            raise AccountTakenDownError(
                f"Auth failed for {handle} — check BSKY_HANDLE / BSKY_APP_PW in Credentials row {ACCOUNT_ROW}."
            ) from exc
        raise

    _write_account_status("Active")

    if cfg["enable_report"]:
        run_report(client, handle, cfg)

    preferred = choose_media_kind()
    print(f"Post-type chosen for this cycle: {preferred}")

    # ── previewLink path ────────────────────────────────────────────────
    if preferred == "previewLink":
        entry = pick_next_url()
        if entry is None:
            print("No unposted rows left in LinkPlan — falling back to image/video this cycle.")
            preferred = random.choice(["image", "video"])
        else:
            if not claim_url_row(entry):
                print("Lost claim race on this LinkPlan row; will try again next cycle.")
                return

            tags = get_account_hashtags() if cfg["hashtags_enabled_link"] else []
            try:
                post_link_card(
                    client, entry["url"], entry["caption"], tags,
                    cfg["preview_timeout"], cfg["max_thumb_bytes"],
                    auto_caption_enabled=cfg["auto_caption_enabled_link"],
                )
            except Exception as exc:
                err = str(exc)
                release_url_claim(entry)
                if "AccountTakedown" in err or "AccountSuspended" in err:
                    raise AccountTakenDownError(f"Account {handle} taken down mid-cycle.") from exc
                print(f"previewLink post failed for {entry['url']} — claim released: {exc}")
                raise

            mark_url_posted(entry)
            return

    # ── image/video path ────────────────────────────────────────────────
    plan = load_post_plan()
    if not plan:
        raise NoMediaFoundError("Post-plan sheet has no usable rows.")

    fallback = "video" if preferred == "image" else "image"

    file, path, kind, caption, row_num = fetch_media_matching_plan(preferred, plan)
    if not file:
        print(f"No {preferred} matched; trying {fallback}.")
        file, path, kind, caption, row_num = fetch_media_matching_plan(fallback, plan)

    if not file:
        raise NoMediaFoundError("No unposted Mega file matching the post-plan sheet.")

    original_name = file["original_name"]
    claimed_name  = file["claimed_name"]

    try:
        if kind == "image":
            path = compress_image_under_limit(path)
        elif kind == "video":
            path = ensure_real_mp4(path)

        cfg = _cfg()
        hashtags_on = cfg["hashtags_enabled_image"] if kind == "image" else cfg["hashtags_enabled_video"]
        tags = get_account_hashtags() if hashtags_on else []
        add_link = should_add_link(kind)

        # The raw sheet caption is passed through; CAPTION_MODE / CAPTION_ENABLED
        # are applied inside resolve_body_caption().
        path = post_to_bluesky(client, original_name, path, kind, caption, tags, add_link)

    except Exception as exc:
        err = str(exc)
        if "AccountTakedown" in err or "AccountSuspended" in err:
            release_claim(claimed_name, original_name)
            raise AccountTakenDownError(f"Account {handle} taken down mid-cycle.") from exc
        release_claim(claimed_name, original_name)
        _BAD_MEDIA[original_name] = _BAD_MEDIA.get(original_name, 0) + 1
        if _BAD_MEDIA[original_name] >= 2:
            print(f"'{original_name}' has failed {_BAD_MEDIA[original_name]}x — skipping it for the rest of this run.")
        print(f"Post failed — claim released, file stays in upload folder.")
        raise

    mark_posted(original_name, row_num)
    move_file_to_processed(claimed_name, original_name)
    if kind == "video":
        increment_video_count()
    try:
        os.remove(path)
    except OSError:
        pass


def main():
    global ACCOUNT_ROW

    if START_JITTER_MAX_SECONDS > 0:
        delay = random.uniform(0, START_JITTER_MAX_SECONDS)
        print(f"Startup jitter: sleeping {delay:.1f}s to spread out Sheets API bursts "
              f"across parallel account jobs…")
        time.sleep(delay)

    try:
        ensure_required_tabs()
        ensure_extra_columns(CREDS_TAB, [
            "PROXY_IP", "PROXY_PORT", "PROXY_ASSIGNED_AT",
            "VIDEO_COUNT_TODAY", "VIDEO_COUNT_DATE",
        ])
        ensure_extra_columns(PROXIES_TAB, PROXY_TRACKING_COLUMNS)
        ensure_settings_defaults()
        ensure_report_header()
        ACCOUNT_ROW = resolve_account_row()
        load_account_config()
    except Exception as exc:
        print(f"\n{'='*60}\nFATAL: {exc}\n{'='*60}\n")
        sys.exit(1)

    print_config_summary()
    print(f"Starting loop. Loop interval, post-type mix and caption mode are read from the "
          f"Settings tab of the Google Sheet and re-checked at the start of "
          f"every cycle — edit them there any time, no redeploy needed.")

    while True:
        cycle_start = time.time()
        try:
            run_once()
        except AccountLockedElsewhereError as exc:
            print(f"\n{'='*60}\n{exc}\nSkipping — schedule keeps running.\n{'='*60}\n")
            sys.exit(0)
        except NoProxyAvailableError as exc:
            print(f"\n{'='*60}\n{exc}\nSkipping this cycle — schedule keeps running.\n{'='*60}\n")
            sys.exit(0)
        except NoMediaFoundError as exc:
            print(f"\n{'='*60}\nNO MEDIA: {exc}\nStopping — schedule keeps running.\n{'='*60}\n")
            sys.exit(0)
        except AccountTakenDownError as exc:
            handle  = (_account_config or {}).get("handle", "unknown")
            err_str = str(exc)
            reason  = ("🔑 AUTH FAILED — check handle/app-password in sheet"
                       if "Auth failed" in err_str or "app password" in err_str
                       else "⛔ ACCOUNT TAKEN DOWN / BANNED")
            print(f"\n{'='*60}\n{err_str}\n→ {reason}\n{'='*60}\n")
            _write_account_status(reason)
            log_account_problem(handle, status=reason)
            ip, port = (_account_config or {}).get("proxy_ip", ""), (_account_config or {}).get("proxy_port", "")
            if ip and port:
                release_or_kill_proxy(ip, port, alive=True)
                _clear_account_proxy()
            with open("ACCOUNT_BANNED", "w") as f:
                f.write(f"{handle}: {reason}\n")
            sys.exit(1)
        except Exception as exc:
            # Includes exhausted-quota-retry-budget errors from sheets_call().
            # A bad cycle costs one cycle, not the account.
            print(f"Error during cycle: {type(exc).__name__}: {exc}")
            traceback.print_exc()

        loop_interval = (_account_config or {}).get("loop_interval_seconds", DEFAULT_LOOP_INTERVAL_SECONDS)
        loop_interval = loop_interval + random.uniform(0, min(30, loop_interval * 0.05))
        elapsed   = time.time() - cycle_start
        sleep_for = max(0, loop_interval - elapsed)
        print(f"Cycle done in {elapsed:.1f}s. Sleeping {sleep_for:.1f}s "
              f"(interval={loop_interval:.0f}s from Settings tab, plus jitter)…")
        time.sleep(sleep_for)


if __name__ == "__main__":
    if "--discover" in sys.argv:
        run_discover()
    else:
        main()
