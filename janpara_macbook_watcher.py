#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import re
import json
import time
import random
import smtplib
import logging
import unicodedata
from email.mime.text import MIMEText
from email.utils import formatdate
from pathlib import Path
from urllib.parse import urlparse, parse_qsl, urlencode, urlunparse, urljoin

import requests
from bs4 import BeautifulSoup, XMLParsedAsHTMLWarning
from dotenv import load_dotenv
import warnings

warnings.filterwarnings("ignore", category=XMLParsedAsHTMLWarning)

# =========================
# .env LOADING
# =========================
HERE = Path(__file__).resolve().parent
ENV_PATH = HERE / ".env"
load_dotenv(dotenv_path=ENV_PATH, override=True)

# =========================
# CONFIG
# =========================
BASE_URL = "https://www.janpara.co.jp"

SORT_ORDER = "4"         # 4=newest first on your smartphone watcher (works here too)
MAX_PAGES = 20
REQUEST_DELAY_SEC = 1.3
HTTP_TIMEOUT_SEC = 20

MAX_RETRIES = 5
BACKOFF_BASE = 1.8
JITTER_RATIO = 0.20
RETRY_STATUS = {429, 500, 502, 503, 504}

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/134.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "ja,en;q=0.9",
    "Accept-Encoding": "gzip, deflate, br",
    "Cache-Control": "no-cache",
    "Pragma": "no-cache",
    "Connection": "keep-alive",
    "Upgrade-Insecure-Requests": "1",
    "Sec-Fetch-Dest": "document",
    "Sec-Fetch-Mode": "navigate",
    "Sec-Fetch-Site": "same-origin",
    "Sec-Fetch-User": "?1",
    "Referer": "https://www.janpara.co.jp/",
}

# MacBook filter requirements
REQUIRE_APPLE_SILICON = False
MIN_RAM_GB = 16

# Busy-page detection
BUSY_PHRASES = [
    "アクセス集中により大変混み合っております。",
    "しばらく時間をおいてから再度お越し下さい",
    "Service Temporarily Unavailable",
]
BUSY_RETRY_AFTER_CAP_SEC = 30


class BusyResponseError(Exception):
    def __init__(self, message: str, items: list | None = None):
        super().__init__(message)
        self.items = items or []


SESSION = requests.Session()
SESSION.headers.update(HEADERS)
SESSION_PRIMED = False

# State file
STATE_FILE = (HERE / "state" / "janpara_macbook_seen.json")
HEARTBEAT_FILE = (HERE / "state" / "janpara_macbook_heartbeat.txt")
HEARTBEAT_INTERVAL_HOURS = int(os.getenv("HEARTBEAT_INTERVAL_HOURS", "24"))
STATE_FILE.parent.mkdir(parents=True, exist_ok=True)

# Feed base URL (your link, but we let build_page_url inject ORDER/PAGE/LINE/cache_key)
MACBOOK_FEED = {
    "name": "MacBook (RAM>=16GB)",
    "url": "https://www.janpara.co.jp/sale/search/result/?KEYWORDS=MacBook&OUTCLSCODE=4&SSHPCODE=&MINPRICE=&MAXPRICE=&ORDER=3&CHKOUTCOM=1&LINE=24",
    "paginate": True,
    "pagination": {"param": "PAGE", "cache_key": "/sale/search/result/", "require_page1": True},
}

# =========================
# TEXT HELPERS
# =========================
def clean_text(text: str) -> str:
    if not text:
        return ""
    text = unicodedata.normalize("NFKC", text)
    return re.sub(r"\s+", " ", text).strip()

def normalize_url(url: str) -> str:
    return urljoin(BASE_URL, url)

# =========================
# PRICE HELPERS
# =========================
PRICE_RE = re.compile(r"¥?\s?(\d{1,3}(?:,\d{3})+)\s*~?")
LABELED_PRICE_RE = re.compile(r"(未使用|新品|中古)\s*[:：]?\s*¥?\s?(\d{1,3}(?:,\d{3})+)\s*~?", re.IGNORECASE)

def extract_prices_with_labels(text: str):
    results, labeled_spans = [], set()
    if not text:
        return results
    for m in LABELED_PRICE_RE.finditer(text):
        results.append({"label": m.group(1), "value": m.group(2)})
        labeled_spans.add(m.span(2))
    for m in PRICE_RE.finditer(text):
        if m.span(1) in labeled_spans:
            continue
        results.append({"label": None, "value": m.group(1)})
    return results

def choose_best_price(prices):
    if not prices:
        return ""
    to_int = lambda v: int(v.replace(",", ""))
    used = [p for p in prices if p["label"] and "中古" in p["label"]]
    if used:
        return f"¥{min(used, key=lambda p: to_int(p['value']))['value']}"
    labeled = [p for p in prices if p["label"]]
    if labeled:
        return f"¥{min(labeled, key=lambda p: to_int(p['value']))['value']}"
    return f"¥{min(prices, key=lambda p: to_int(p['value']))['value']}"

def extract_all_price_ints(text: str):
    ints = []
    for m in PRICE_RE.finditer(text or ""):
        try:
            ints.append(int(m.group(1).replace(",", "")))
        except Exception:
            pass
    return ints

def price_to_int(price_str: str) -> int:
    if not price_str:
        return 0
    m = re.search(r"(\d{1,3}(?:,\d{3})+)", price_str)
    return int(m.group(1).replace(",", "")) if m else 0

def ascii_price(p: str) -> str:
    if not p:
        return p
    y = p.replace("円", "").replace("¥", "").strip()
    return f"{y} JPY"

# =========================
# ATTR HELPERS
# =========================
def extract_itmcode(url: str) -> str | None:
    m = re.search(r"[?&]ITMCODE=(\d+)", url)
    return m.group(1) if m else None

COND_RE = re.compile(r"(未使用|新品|中古\s*[SABC]?)", re.IGNORECASE)
def extract_condition(text: str) -> str | None:
    m = COND_RE.search(text or "")
    if not m:
        return None
    token = m.group(1).replace(" ", "")
    if token.startswith(("未使用", "新品")):
        return "Unused"
    if token.startswith("中古"):
        g = re.search(r"中古\s*([SABC])", token, re.IGNORECASE)
        return f"Used{(' ' + g.group(1)) if g else ''}"
    return None

STOCK_RE = re.compile(r"(\d+)\s*個の?在庫|在庫\s*(\d+)\s*個")
def extract_stock_count(text: str) -> int | None:
    m = STOCK_RE.search(text or "")
    if not m:
        return None
    val = m.group(1) or m.group(2)
    try:
        return int(val)
    except Exception:
        return None

# ---- MacBook specific extraction ----
APPLE_SILICON_RE = re.compile(r"\b(?:Apple\s*)?M(\d)\b", re.IGNORECASE)
APPLE_SILICON_VARIANT_RE = re.compile(r"\bM(\d)\s*(Pro|Max|Ultra)\b", re.IGNORECASE)

RAM_CONTEXT_RE = re.compile(r"(?:ram|memory|メモリ|メモリー|メモリー容量|記憶装置|memory\s+size)", re.IGNORECASE)
RAM_PATTERNS = [
    (re.compile(r"メモリ\s*[:：]?\s*(\d{1,3})\s*G[B]?", re.IGNORECASE), False),
    (re.compile(r"\bRAM\s*[:：]?\s*(\d{1,3})\s*GB\b", re.IGNORECASE), False),
    (re.compile(r"\b(\d{1,3})\s*GB\s+RAM\b", re.IGNORECASE), False),
    (re.compile(r"/\s*(\d{1,3})\s*G\s*/", re.IGNORECASE), True),
    (re.compile(r"\b(\d{1,3})\s*G\b", re.IGNORECASE), True),
    (re.compile(r"\b(\d{1,3})\s*GB\b", re.IGNORECASE), True),
]

def is_apple_silicon(text: str) -> bool:
    if not text:
        return False
    return bool(APPLE_SILICON_VARIANT_RE.search(text) or APPLE_SILICON_RE.search(text))

def extract_cpu_label(text: str) -> str:
    if not text:
        return ""
    m = APPLE_SILICON_VARIANT_RE.search(text)
    if m:
        return f"M{m.group(1)} {m.group(2)}"
    m = APPLE_SILICON_RE.search(text)
    if m:
        return f"M{m.group(1)}"
    return ""

def extract_ram_gb(text: str) -> int | None:
    if not text:
        return None
    for rx, require_context in RAM_PATTERNS:
        m = rx.search(text)
        if not m:
            continue
        if require_context:
            span = m.span(1)
            ctx = text[max(0, span[0] - 40): span[1] + 40]
            if not RAM_CONTEXT_RE.search(ctx):
                continue
        try:
            return int(m.group(1))
        except Exception:
            pass
    return None

KBD_JP_RE = re.compile(r"(JIS|日本語|かな|JPN|JP配列)", re.IGNORECASE)
KBD_US_RE = re.compile(r"(\bUS\b|ANSI|英語|英字|US配列|英語配列)", re.IGNORECASE)

def detect_keyboard_layout(text: str) -> str:
    if not text:
        return ""
    if KBD_JP_RE.search(text):
        return "JP"
    if KBD_US_RE.search(text):
        return "US"
    return ""

# =========================
# RETRIES / BUSY
# =========================
def _sleep_with_jitter(base: float, attempt: int):
    wait = base ** (attempt - 1)
    jitter = wait * random.uniform(-JITTER_RATIO, JITTER_RATIO)
    time.sleep(max(0.5, wait + jitter))

def is_busy_response(resp: requests.Response) -> bool:
    if resp.status_code in RETRY_STATUS:
        return True
    content_type = (resp.headers.get("Content-Type") or "").lower()
    if content_type and "html" not in content_type and "text" not in content_type:
        return False
    try:
        text = clean_text(resp.text[:4000]).lower()
    except Exception:
        return False
    return any(p.lower() in text for p in BUSY_PHRASES)

def log_response_debug(resp: requests.Response, prefix: str):
    try:
        snippet = clean_text(resp.text[:500])
    except Exception:
        snippet = ""
    if snippet:
        logging.warning("%s: status=%s content_type=%s body=%s", prefix, resp.status_code, resp.headers.get("Content-Type", ""), snippet)
    else:
        logging.warning("%s: status=%s content_type=%s", prefix, resp.status_code, resp.headers.get("Content-Type", ""))

def prime_session(force: bool = False):
    global SESSION_PRIMED
    if SESSION_PRIMED and not force:
        return
    try:
        SESSION.get(BASE_URL + "/", timeout=HTTP_TIMEOUT_SEC)
        SESSION_PRIMED = True
    except Exception as e:
        logging.debug("Session prime failed: %s", e)

def request_get_with_retries(url: str) -> requests.Response:
    last_exc = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            if attempt == 1:
                prime_session()
            r = SESSION.get(url, timeout=HTTP_TIMEOUT_SEC)
            if r.status_code == 403:
                log_response_debug(r, f"403 on attempt {attempt} for {url}")
                prime_session(force=True)
                last_exc = requests.HTTPError(f"{r.status_code} {r.reason}")
                if attempt >= MAX_RETRIES:
                    break
                _sleep_with_jitter(BACKOFF_BASE, attempt)
                continue
            if is_busy_response(r):
                ra = r.headers.get("Retry-After")
                if ra:
                    try:
                        time.sleep(min(int(ra), BUSY_RETRY_AFTER_CAP_SEC))
                    except Exception:
                        _sleep_with_jitter(BACKOFF_BASE, attempt)
                else:
                    _sleep_with_jitter(BACKOFF_BASE, attempt)
                last_exc = BusyResponseError("Busy response: site overloaded")
                continue
            if r.status_code in RETRY_STATUS:
                ra = r.headers.get("Retry-After")
                if ra:
                    try:
                        time.sleep(min(int(ra), BUSY_RETRY_AFTER_CAP_SEC))
                    except Exception:
                        _sleep_with_jitter(BACKOFF_BASE, attempt)
                else:
                    _sleep_with_jitter(BACKOFF_BASE, attempt)
                last_exc = requests.HTTPError(f"{r.status_code} {r.reason}")
                continue
            r.raise_for_status()
            return r
        except (requests.Timeout, requests.ConnectionError, requests.HTTPError) as e:
            last_exc = e
            if attempt >= MAX_RETRIES:
                break
            _sleep_with_jitter(BACKOFF_BASE, attempt)
    raise last_exc if last_exc else RuntimeError("request_get_with_retries failed")

# =========================
# PARSING
# =========================
def is_detail_link(href: str) -> bool:
    if not href:
        return False
    hl = href.lower()
    if "type=rec" in hl or "srcode=" in hl:
        return False
    return "itmcode=" in hl

def fetch_listing_items(url: str) -> list[dict]:
    r = request_get_with_retries(url)
    soup = BeautifulSoup(r.content, "lxml", from_encoding="utf-8")
    return parse_listing_cards(soup)

def parse_listing_cards(soup: BeautifulSoup) -> list[dict]:
    items = {}

    for a in soup.find_all("a", href=True):
        href = a["href"]
        if not is_detail_link(href):
            continue

        full = normalize_url(href)
        itmcode = extract_itmcode(full)
        if not itmcode:
            continue

        # find a reasonable container block
        container = a
        for _ in range(4):
            container = container.parent
            if container is None:
                break
            if hasattr(container, "get_text") and len(list(container.descendants)) > 20:
                break

        block_text = container.get_text(" ", strip=True) if container else a.get_text(" ", strip=True)
        block_text = clean_text(block_text)

        # title candidate
        title = clean_text(a.get_text(" ", strip=True)) or block_text[:200] or full

        # prices
        price_list = extract_prices_with_labels(block_text)
        price_raw = choose_best_price(price_list)
        all_ints = extract_all_price_ints(block_text)
        min_price_int = min(all_ints) if all_ints else None

        # store
        store = ""
        m = re.search(r"(\S+店)", block_text)
        if m:
            store = clean_text(m.group(1))

        condition = extract_condition(block_text) or ""
        stock = extract_stock_count(block_text)

        # quick extract from listing text (we will still confirm from detail page later)
        cpu = extract_cpu_label(block_text) or extract_cpu_label(title)
        ram_gb = extract_ram_gb(block_text) or extract_ram_gb(title) or 0
        kbd = detect_keyboard_layout(block_text) or detect_keyboard_layout(title)

        items[itmcode] = {
            "id": itmcode,
            "title": title,
            "price": ascii_price(price_raw) if price_raw else (f"{min_price_int:,} JPY" if min_price_int else ""),
            "min_price_int": min_price_int if min_price_int is not None else price_to_int(price_raw),
            "store": store,
            "href": full,
            "condition": condition,
            "stock": stock,
            "cpu": cpu,
            "ram_gb": ram_gb,
            "kbd": kbd,
        }

    return list(items.values())

# =========================
# DETAIL ENRICHMENT (CPU/RAM/KBD)
# =========================
def fetch_detail_text(url: str) -> str:
    r = request_get_with_retries(url)
    soup = BeautifulSoup(r.content, "lxml", from_encoding="utf-8")
    return clean_text(soup.get_text(" ", strip=True))

def enrich_from_detail(item: dict, cache: dict) -> dict:
    url = item.get("href") or ""
    if not url:
        return item
    if url in cache:
        text = cache[url]
    else:
        text = fetch_detail_text(url)
        cache[url] = text

    # fill missing or strengthen
    item["cpu"] = item.get("cpu") or extract_cpu_label(text)
    item["ram_gb"] = int(item.get("ram_gb") or 0) or int(extract_ram_gb(text) or 0)
    item["kbd"] = item.get("kbd") or detect_keyboard_layout(text)

    return item

# =========================
# URL & PAGINATION
# =========================
def _with_params(url: str, **extra):
    parts = urlparse(url)
    q = parse_qsl(parts.query, keep_blank_values=True)
    multi = {}
    for k, v in q:
        multi.setdefault(k, []).append(v)
    for k, v in extra.items():
        if isinstance(v, list):
            multi[k] = v
        elif v is None:
            if k in multi:
                del multi[k]
        else:
            multi[k] = [str(v)]
    new_query = urlencode(multi, doseq=True)
    return urlunparse(parts._replace(query=new_query))

def build_page_url(feed: dict, page: int) -> str:
    base_url = feed["url"]
    pg = feed.get("pagination", {})
    page_param = pg.get("param", "PAGE")
    cache_key_val = pg.get("cache_key", "/sale/search/result/")
    require_page1 = pg.get("require_page1", False)

    if page == 1:
        if require_page1:
            return _with_params(base_url,
                                **{page_param: "1",
                                   "cache_key": cache_key_val,
                                   "ORDER": SORT_ORDER,
                                   "LINE": "24"})
        else:
            return _with_params(base_url, ORDER=SORT_ORDER, LINE="24")

    return _with_params(base_url,
                        **{page_param: str(page),
                           "cache_key": cache_key_val,
                           "ORDER": SORT_ORDER,
                           "LINE": "24"})

def fetch_feed_all_pages(feed: dict, max_pages: int = MAX_PAGES) -> list[dict]:
    all_items = []
    name = feed["name"]
    for page in range(1, max_pages + 1):
        url = build_page_url(feed, page)
        try:
            page_items = fetch_listing_items(url)
        except BusyResponseError as e:
            logging.warning("%s: busy response on page %d; stopping early", name, page)
            raise BusyResponseError(str(e), items=all_items)
        except Exception as e:
            logging.warning("%s: page %d fetch/parse error -> %s", name, page, e)
            break
        logging.debug("%s: page %d -> %d raw items", name, page, len(page_items))
        if not page_items:
            break
        all_items.extend(page_items)
        time.sleep(max(0.5, REQUEST_DELAY_SEC * random.uniform(1 - JITTER_RATIO, 1 + JITTER_RATIO)))
    return all_items

# =========================
# STATE + DIFF (ITMCODE + PRICE DROPS)
# =========================
def load_state():
    """
    state = {
      "seen_itmcodes": [...],
      "last_min_price_by_code": {"12345": 198000, ...}
    }
    """
    if STATE_FILE.exists():
        try:
            s = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        except Exception:
            s = {}
    else:
        s = {}
    s.setdefault("seen_itmcodes", [])
    s.setdefault("last_min_price_by_code", {})
    s["seen_itmcodes"] = sorted(set(str(x) for x in s["seen_itmcodes"]))
    # normalize price map
    norm = {}
    for k, v in (s.get("last_min_price_by_code") or {}).items():
        try:
            norm[str(k)] = int(v)
        except Exception:
            pass
    s["last_min_price_by_code"] = norm
    return s

def save_state(state):
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")

def diff_new_and_drops(current_items: list, state: dict):
    seen = set(state.get("seen_itmcodes", []))
    last_min = dict(state.get("last_min_price_by_code", {}))

    new_items = []
    drops = []

    for it in current_items:
        code = str(it["id"])
        cur_min = int(it.get("min_price_int") or price_to_int(it.get("price", "")) or 0)

        if code not in seen:
            new_items.append(it)
            seen.add(code)
        else:
            prev = last_min.get(code)
            if prev is not None and cur_min and cur_min < prev:
                drops.append({**it, "previous_min": prev})

        if cur_min:
            last_min[code] = cur_min

    state["seen_itmcodes"] = sorted(seen)
    state["last_min_price_by_code"] = last_min
    return new_items, drops, state

# =========================
# FILTERS
# =========================
def passes_macbook_requirements(item: dict) -> bool:
    ram = int(item.get("ram_gb") or 0)
    if ram and ram < MIN_RAM_GB:
        return False
    # If RAM is unknown (0), we will try detail enrichment before rejecting.
    return True

# =========================
# EMAIL
# =========================
def format_email_body(new_items: list, drop_items: list, note: str = "") -> str:
    def as_price(i):
        val = int(i.get("min_price_int") or price_to_int(i.get("price", "")) or 0)
        return val if val > 0 else 10**18

    def append_items_by_ram(title: str, items: list, is_drop: bool = False) -> None:
        if not items:
            return
        lines.append(title)
        by_ram = {}
        for it in items:
            ram = int(it.get("ram_gb") or 0)
            by_ram.setdefault(ram, []).append(it)
        for ram in sorted(by_ram.keys(), key=lambda r: (r == 0, -r)):
            label = f"{ram}GB RAM" if ram else "Unknown RAM"
            lines.append(f"  {label}")
            for it in sorted(by_ram[ram], key=as_price):
                lines.append(f"- {it['title']}")
                if is_drop:
                    prev = int(it.get("previous_min") or 0)
                    now = as_price(it)
                    delta = f"-{(prev - now):,} JPY" if (prev and now and prev > now) else ""
                    lines.append(f"  Now: {it.get('price','')}  {delta}".strip())
                else:
                    if it.get("price"):
                        lines.append(f"  Price: {it['price']}")
                ram_label = f"{int(it.get('ram_gb') or 0)}GB RAM" if it.get("ram_gb") else "Unknown RAM"
                lines.append(f"  Spec: {it.get('cpu','')}, {ram_label}")
                if it.get("kbd"):
                    lines.append(f"  Keyboard: {it['kbd']} (JP=JIS / US=ANSI)")
                if it.get("condition"):
                    lines.append(f"  Condition: {it['condition']}")
                stock = it.get("stock")
                lines.append(f"  Stock: {stock if stock is not None else 'unknown'}")
                if it.get("store"):
                    lines.append(f"  Store: {it['store']}")
                lines.append(f"  Link: {it['href']}")
                lines.append("")

    lines = []
    lines.append("Janpara MacBook alerts")
    lines.append(f"Filters: RAM >= {MIN_RAM_GB}GB")
    if note:
        lines.append(note)
    lines.append("")

    append_items_by_ram("— Price drops —", drop_items, is_drop=True)
    append_items_by_ram("— New listings —", new_items, is_drop=False)

    if not new_items and not drop_items:
        lines.append("No new items or price drops this run.")

    return "\n".join(lines).strip()

def send_email(subject: str, body: str):
    smtp_host = os.environ.get("SMTP_HOST", "")
    smtp_port = int(os.environ.get("SMTP_PORT", "587"))
    smtp_user = os.environ.get("SMTP_USER", "")
    smtp_pass = os.environ.get("SMTP_PASS", "")
    from_email = os.environ.get("FROM_EMAIL", smtp_user)
    to_emails = [e.strip() for e in os.environ.get("TO_EMAILS", "").split(",") if e.strip()]
    if not (smtp_host and smtp_user and smtp_pass and to_emails):
        raise RuntimeError("SMTP or recipient configuration missing. Check your .env file.")

    msg = MIMEText(body, _charset="utf-8")
    msg["Subject"] = subject
    msg["From"] = from_email
    msg["To"] = ", ".join(to_emails)
    msg["Date"] = formatdate(localtime=True)

    with smtplib.SMTP(smtp_host, smtp_port, timeout=30) as s:
        s.ehlo()
        s.starttls()
        s.login(smtp_user, smtp_pass)
        s.sendmail(from_email, to_emails, msg.as_string())

def mark_heartbeat_now():
    try:
        HEARTBEAT_FILE.write_text(str(int(time.time())), encoding="utf-8")
    except Exception as e:
        logging.warning("Failed to update heartbeat file: %s", e)

def maybe_send_heartbeat(subject: str, body: str):
    if HEARTBEAT_INTERVAL_HOURS <= 0:
        return
    now = int(time.time())
    interval_sec = HEARTBEAT_INTERVAL_HOURS * 3600
    last_sent = 0
    try:
        last_sent = int((HEARTBEAT_FILE.read_text(encoding="utf-8") or "0").strip())
    except Exception:
        last_sent = 0
    if now - last_sent < interval_sec:
        return
    send_email(subject, body)
    mark_heartbeat_now()
    logging.info("Heartbeat email sent.")

# =========================
# MAIN
# =========================
def main():
    log_level = os.getenv("LOG_LEVEL", "INFO").upper()
    logging.basicConfig(
        level=getattr(logging, log_level, logging.INFO),
        format="%(asctime)s %(levelname)s %(message)s"
    )

    state = load_state()
    detail_cache = {}
    busy_stop = False

    logging.info("Fetching: %s", MACBOOK_FEED["name"])
    try:
        items = fetch_feed_all_pages(MACBOOK_FEED, max_pages=MAX_PAGES)
    except BusyResponseError as e:
        logging.warning("Busy response while fetching listings; sending partial results.")
        items = e.items
        busy_stop = True

    # Dedup by ITMCODE (keep first)
    dedup = []
    seen = set()
    for it in items:
        code = str(it["id"])
        if code in seen:
            continue
        seen.add(code)
        dedup.append(it)
    items = dedup

    # First pass: keep listings around until detail verification (don’t reject RAM=0 yet)
    candidates = []
    for it in items:
        candidates.append(it)

    # Enrich from detail page so we can confirm RAM & keyboard layout
    enriched = []
    if busy_stop:
        enriched = candidates
    else:
        for idx, it in enumerate(candidates):
            try:
                enrich_from_detail(it, detail_cache)
            except BusyResponseError:
                logging.warning("Busy response while fetching details; sending partial results.")
                busy_stop = True
                enriched.append(it)
                enriched.extend(candidates[idx + 1:])
                break
            except Exception as e:
                logging.debug("Detail fetch failed (%s): %s", it.get("href",""), e)
            enriched.append(it)
            time.sleep(max(0.5, REQUEST_DELAY_SEC * random.uniform(1 - JITTER_RATIO, 1 + JITTER_RATIO)))

    # Apply final strict filters
    filtered = []
    for it in enriched:
        ram = int(it.get("ram_gb") or 0)
        if ram and ram < MIN_RAM_GB:
            continue
        if not ram and not busy_stop:
            continue
        if it.get("stock") == 0:
            continue
        filtered.append(it)

    logging.info("Filtered items: %d", len(filtered))

    if busy_stop:
        note = "Busy response encountered; sending partial results from this run."
        new_items, drop_items, state = diff_new_and_drops(filtered, state)
        save_state(state)
        if new_items or drop_items:
            body = format_email_body(new_items, drop_items, note=note)
            send_email("[Janpara] MacBook alerts (RAM>=16GB, partial run)", body)
            mark_heartbeat_now()
            logging.info("Email sent (partial).")
        else:
            logging.info("No new items or price drops in partial run.")
            maybe_send_heartbeat(
                "[Janpara] MacBook heartbeat (degraded run)",
                "Janpara MacBook watcher completed with degraded status: busy response encountered and no alertable changes found.",
            )
        return

    new_items, drop_items, state = diff_new_and_drops(filtered, state)

    logging.info("New: %d | Drops: %d", len(new_items), len(drop_items))

    if new_items or drop_items:
        body = format_email_body(new_items, drop_items)
        send_email("[Janpara] MacBook alerts (RAM>=16GB)", body)
        mark_heartbeat_now()
        logging.info("Email sent.")
    else:
        logging.info("No alerts.")
        maybe_send_heartbeat(
            "[Janpara] MacBook heartbeat (no changes)",
            "Janpara MacBook watcher is healthy. No new items or price drops in recent runs.",
        )

    save_state(state)

if __name__ == "__main__":
    main()
