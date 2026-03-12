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

# Silence "XMLParsedAsHTMLWarning" from BeautifulSoup (pages are HTML)
warnings.filterwarnings("ignore", category=XMLParsedAsHTMLWarning)

# =========================
# .env LOADING (for local runs; Actions uses env secrets)
# =========================
HERE = Path(__file__).resolve().parent
ENV_PATH = HERE / ".env"
load_dotenv(dotenv_path=ENV_PATH, override=True)

# =========================
# CONFIG
# =========================
BASE_URL = "https://www.janpara.co.jp"

SORT_ORDER = "4"         # ORDER=4 → newest first
MAX_PAGES = 20
REQUEST_DELAY_SEC = 1.3
HTTP_TIMEOUT_SEC = 20
REQUIRE_PRICE = True
ONLY_SMARTPHONE_DETAIL = True  # still respected, plus stricter ITMCODE check

# HTTP / retries
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

SESSION = requests.Session()
SESSION.headers.update(HEADERS)
SESSION_PRIMED = False

STATE_FILE = (HERE / "state" / "janpara_ipad_seen.json")
HEARTBEAT_FILE = (HERE / "state" / "janpara_ipad_heartbeat.txt")
HEARTBEAT_INTERVAL_HOURS = int(os.getenv("HEARTBEAT_INTERVAL_HOURS", "24"))
STATE_FILE.parent.mkdir(parents=True, exist_ok=True)

# Feeds
FEEDS = [
    {
        "name": "Apple iPad",
        "url": "https://www.janpara.co.jp/sale/search/result/?KEYWORDS=&OUTCLSCODE=79&SSHPCODE=&MINPRICE=&MAXPRICE=&ORDER=3&CHKOUTCOM=1&PRBFLTWORD01_FILTER%5B%5D=2&PRBFLTWORD01_FILTER%5B%5D=3&PRBFLTWORD01_FILTER%5B%5D=4&PRBFLTWORD01_FILTER%5B%5D=5&PRBFLTWORD01_FILTER%5B%5D=6&PRBFLTWORD01_FILTER%5B%5D=7&PRBFLTWORD01_FILTER%5B%5D=2&PRBFLTWORD01_FILTER%5B%5D=3&PRBFLTWORD01_FILTER%5B%5D=4&PRBFLTWORD01_FILTER%5B%5D=5&PRBFLTWORD01_FILTER%5B%5D=6&PRBFLTWORD01_FILTER%5B%5D=7&PRBFLT642_FILTER%5B%5D=0&PRBFLT642_FILTER%5B%5D=1&LINE=24",
        "paginate": True,
        "pagination": {"param": "PAGE", "cache_key": "/sale/search/result/", "require_page1": True},
    },
]

# Busy-page detection
BUSY_PHRASES = [
    "アクセス集中により大変混み合っております。",
    "しばらく時間をおいてから再度お越し下さい",
    "Service Temporarily Unavailable",
]

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

def ascii_price(p: str) -> str:
    if not p:
        return p
    y = p.replace("円", "").replace("¥", "").strip()
    return f"{y} JPY"

def price_to_int(price_str: str) -> int:
    if not price_str:
        return 0
    m = re.search(r"(\d{1,3}(?:,\d{3})+)", price_str)
    return int(m.group(1).replace(",", "")) if m else 0

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

# =========================
# GENERAL HELPERS
# =========================
def load_state():
    """
    state[feed] = {
      "seen_itmcodes": ["315412", ...],
      "last_min_price_by_code": {"315412": 5980, ...}
    }
    """
    if STATE_FILE.exists():
        try:
            state = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        except Exception:
            state = {}
    else:
        state = {}

    # normalize shape
    changed = False
    new_state = {}
    for feed, entry in list(state.items()):
        fs = {"seen_itmcodes": [], "last_min_price_by_code": {}}
        if isinstance(entry, dict):
            if isinstance(entry.get("seen_itmcodes"), list):
                fs["seen_itmcodes"] = [str(x) for x in entry["seen_itmcodes"]]
            elif isinstance(entry.get("keys"), list):
                fs["seen_itmcodes"] = [str(x) for x in entry["keys"]]; changed = True
            if isinstance(entry.get("last_min_price_by_code"), dict):
                for k, v in entry["last_min_price_by_code"].items():
                    try:
                        fs["last_min_price_by_code"][str(k)] = int(v)
                    except Exception:
                        pass
        elif isinstance(entry, list):
            fs["seen_itmcodes"] = [str(x) for x in entry]; changed = True
        fs["seen_itmcodes"] = sorted(set(fs["seen_itmcodes"]))
        new_state[feed] = fs
    if changed:
        save_state(new_state)
        logging.info("State migration: normalized to ITMCODE-based schema.")
    return new_state if changed else state

def save_state(state):
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")

def is_detail_link(href: str) -> bool:
    """
    Treat any link containing ITMCODE= as a real product detail.
    Explicitly exclude recommendation widgets (TYPE=rec / SRCODE).
    """
    if not href:
        return False
    hl = href.lower()
    if "type=rec" in hl or "srcode=" in hl:
        return False
    return "itmcode=" in hl

def normalize_url(url: str) -> str:
    return urljoin(BASE_URL, url)

def clean_text(text: str) -> str:
    if not text:
        return ""
    text = unicodedata.normalize("NFKC", text)
    return re.sub(r"\s+", " ", text).strip()

# --- retry / busy detection ---
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

def request_get_with_retries(url: str, headers: dict, timeout: int) -> requests.Response:
    last_exc = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            if attempt == 1:
                prime_session()
            r = SESSION.get(url, headers=headers, timeout=timeout)
            if r.status_code == 403:
                log_response_debug(r, f"403 on attempt {attempt} for {url}")
                prime_session(force=True)
                last_exc = requests.HTTPError(f"{r.status_code} {r.reason}")
                if attempt >= MAX_RETRIES:
                    break
                _sleep_with_jitter(BACKOFF_BASE, attempt)
                continue
            if r.status_code in RETRY_STATUS or is_busy_response(r):
                ra = r.headers.get("Retry-After")
                if ra:
                    try:
                        time.sleep(int(ra))
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

def fetch_and_parse(url: str):
    r = request_get_with_retries(url, headers=HEADERS, timeout=HTTP_TIMEOUT_SEC)
    soup = BeautifulSoup(r.content, "lxml", from_encoding="utf-8")
    # DEBUG: show first few candidate hrefs
    debug = [a.get("href","") for a in soup.find_all("a", href=True)]
    logging.debug("Found %d anchors; examples: %s", len(debug), debug[:10])
    return parse_listing_cards(soup)

def parse_listing_cards(soup: BeautifulSoup):
    """
    Returns list of items:
      {id(=ITMCODE), title, price, min_price_int, store, href, condition, stock}
    """
    items = {}

    # Only the brands we care about (used for picking a good title string)
    brand_keywords = [
        "iPad", "Apple",
    ]

    for a in soup.find_all("a", href=True):
        href = a["href"]
        if not is_detail_link(href):
            continue

        full = normalize_url(href)
        itmcode = extract_itmcode(full)
        if not itmcode:
            # Guard: shouldn't happen with the stricter filter, but keep safe fallback
            itmcode = full

        # find a reasonable card container
        container = a
        for _ in range(4):
            container = container.parent
            if container is None:
                break
            if hasattr(container, "get_text") and len(list(container.descendants)) > 20:
                break

        block_text = container.get_text(" ", strip=True) if container else a.get_text(" ", strip=True)

        # title
        title_candidates = []
        if a.get_text(strip=True):
            title_candidates.append(a.get_text(strip=True))
        if block_text:
            title_candidates.append(block_text[:200])

        chosen_title = None
        for t in title_candidates:
            if any(b.lower() in t.lower() for b in brand_keywords) and len(t) >= 6:
                chosen_title = t
                break
        if not chosen_title:
            chosen_title = title_candidates[0] if title_candidates else full
        chosen_title = clean_text(chosen_title)

        # prices
        price_list = extract_prices_with_labels(block_text)
        price_raw = choose_best_price(price_list)
        all_ints = extract_all_price_ints(block_text)
        min_price_int = min(all_ints) if all_ints else None

        if REQUIRE_PRICE and not price_raw and min_price_int is None:
            continue

        # store
        store = ""
        m = re.search(r"(\S+店)", block_text)
        if m:
            store = clean_text(m.group(1))

        condition = extract_condition(block_text) or ""
        stock = extract_stock_count(block_text)

        items[itmcode] = {
            "id": itmcode,
            "title": chosen_title,
            "price": ascii_price(price_raw) if price_raw else (f"{min_price_int:,} JPY" if min_price_int else ""),
            "min_price_int": min_price_int if min_price_int is not None else price_to_int(price_raw),
            "store": store,
            "href": full,
            "condition": condition,
            "stock": stock if stock is not None else 0,
        }

    return list(items.values())

# --- URL & pagination ---
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
            return _with_params(base_url,
                                ORDER=SORT_ORDER,
                                LINE="24")
    return _with_params(base_url,
                            **{page_param: str(page),
                            "cache_key": cache_key_val,
                            "ORDER": SORT_ORDER,
                            "LINE": "24"})

def fetch_feed_all_pages(feed: dict, max_pages: int = MAX_PAGES, stop_on_empty: bool = True):
    all_items = []
    name = feed["name"]
    for page in range(1, max_pages + 1):
        url = build_page_url(feed, page)
        try:
            page_items = fetch_and_parse(url)
        except Exception as e:
            logging.warning("%s: page %d fetch/parse error -> %s", name, page, e)
            break
        logging.debug("%s: page %d -> %d raw items", name, page, len(page_items))
        if not page_items and stop_on_empty:
            break
        all_items.extend(page_items)
        time.sleep(max(0.5, REQUEST_DELAY_SEC * random.uniform(1 - JITTER_RATIO, 1 + JITTER_RATIO)))
    return all_items

def fetch_all_pages_for_url(url: str, pagination: dict | None, max_pages: int) -> list:
    dummy_feed = {"url": url, "pagination": pagination or {}}
    return fetch_feed_all_pages(dummy_feed, max_pages=max_pages)

def filter_items_by_brand(items, must_include=None):
    """For Xiaomi/Google: feed URL already filters → return as-is. For OnePlus: enforce keywords."""
    if not must_include:
        return items
    mi = [m.lower() for m in must_include]
    out = []
    for it in items:
        title = (it.get("title") or "").lower()
        if any(w in title for w in mi):
            out.append(it)
    return out

# --- Diff: new ITMCODEs + price drops (per-ITMCODE min price) ---
def diff_new_and_drops(feed_name: str, current_items: list, state: dict):
    feed_state = state.get(feed_name) or {"seen_itmcodes": [], "last_min_price_by_code": {}}
    seen_codes = set(str(x) for x in feed_state.get("seen_itmcodes", []))
    last_min_map = {str(k): int(v) for k, v in (feed_state.get("last_min_price_by_code") or {}).items()
                    if isinstance(v, (int, float, str)) and str(v).isdigit()}

    new_listings, price_drops = [], []

    for it in current_items:
        code = str(it["id"])
        cur_min = it.get("min_price_int") or price_to_int(it.get("price", "")) or 0

        if code not in seen_codes:
            new_listings.append(it)
            seen_codes.add(code)
        else:
            prev = last_min_map.get(code)
            if prev is not None and cur_min and cur_min < prev:
                price_drops.append({**it, "previous_min": prev})

        if cur_min:
            last_min_map[code] = cur_min

    state[feed_name] = {
        "seen_itmcodes": sorted(seen_codes),
        "last_min_price_by_code": last_min_map,
    }
    return new_listings, price_drops, state

def format_email_body(grouped):
    """Price drops first (sorted asc), then new listings (sorted asc) within each feed."""
    def as_price(i): return price_to_int(i.get("price", "")) or i.get("min_price_int") or 0

    lines = []
    lines.append("Janpara smartphone alerts\n")

    for feed_name, new_items, drop_items in grouped:
        if not new_items and not drop_items:
            continue

        lines.append(f"=== {feed_name} ===")

        if drop_items:
            lines.append("— Price drops —")
            for it in sorted(drop_items, key=as_price):
                prev = it.get("previous_min")
                now = as_price(it)
                delta = f"-{(prev - now):,} JPY" if (prev and now and prev > now) else ""
                lines.append(f"- {it['title']}")
                lines.append(f"  Now: {it['price']}  {delta}")
                if it.get("condition"):
                    lines.append(f"  Condition: {it['condition']}")
                if it.get("stock") is not None:
                    lines.append(f"  Stock: {it['stock']}")
                if it.get("store"):
                    lines.append(f"  Store: {it['store']}")
                lines.append(f"  Link: {it['href']}")
                lines.append("")

        if new_items:
            lines.append("— New listings —")
            for it in sorted(new_items, key=as_price):
                lines.append(f"- {it['title']}")
                if it.get("price"):
                    lines.append(f"  Price: {it['price']}")
                if it.get("condition"):
                    lines.append(f"  Condition: {it['condition']}")
                if it.get("stock") is not None:
                    lines.append(f"  Stock: {it['stock']}")
                if it.get("store"):
                    lines.append(f"  Store: {it['store']}")
                lines.append(f"  Link: {it['href']}")
                lines.append("")

        lines.append("")

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
    msg["Subject"] = "[Janpara] iPad alerts"
    msg["From"] = from_email
    msg["To"] = ", ".join(to_emails)
    msg["Date"] = formatdate(localtime=True)
    with smtplib.SMTP(smtp_host, smtp_port, timeout=30) as s:
        s.ehlo(); s.starttls(); s.login(smtp_user, smtp_pass); s.sendmail(from_email, to_emails, msg.as_string())

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
    logging.basicConfig(level=getattr(logging, log_level, logging.INFO),
                    format="%(asctime)s %(levelname)s %(message)s")

    state = load_state()
    grouped = []
    any_success = False

    for feed in FEEDS:
        name = feed["name"]
        logging.info("Fetching: %s", name)
        items = []

        # Base
        try:
            if feed.get("paginate", False):
                items.extend(fetch_feed_all_pages(feed, max_pages=MAX_PAGES))
            else:
                items.extend(fetch_and_parse(feed["url"]))
            any_success = any_success or bool(items)
        except Exception as e:
            logging.warning("%s: base URL failed (%s). Will try variants if any.", name, e)

        # Variants (OnePlus only)
        for vurl in feed.get("variants", []):
            try:
                logging.info("%s: fetching variant %s", name, vurl)
                if feed.get("paginate", False):
                    items.extend(fetch_all_pages_for_url(vurl, feed.get("pagination"), MAX_PAGES))
                else:
                    items.extend(fetch_and_parse(vurl))
                any_success = any_success or bool(items)
            except Exception as e:
                logging.warning("%s: variant failed (%s): %s", name, vurl, e)

        # Dedup by ITMCODE (keep first)
        dedup, seen = [], set()
        for it in items:
            code = str(it["id"])
            if code in seen:
                continue
            seen.add(code)
            dedup.append(it)
        items = dedup

        # Brand filter (none needed for iPad URL)
        filtered = filter_items_by_brand(items, feed.get("must_include"))

        logging.info("%s: %d items after filter", name, len(filtered))

        new_items, drop_items, state = diff_new_and_drops(name, filtered, state)
        logging.info("%s: new %d | drops %d", name, len(new_items), len(drop_items))

        if new_items or drop_items:
            grouped.append((name, new_items, drop_items))

        time.sleep(max(0.5, REQUEST_DELAY_SEC * random.uniform(1 - JITTER_RATIO, 1 + JITTER_RATIO)))

    if grouped:
        body = format_email_body(grouped)
        send_email("[Janpara] iPad alerts", body)
        mark_heartbeat_now()
        logging.info("Email sent for %d feed groups", len(grouped))
    else:
        if not any_success:
            logging.warning("Run degraded: all feeds failed or returned busy pages.")
            maybe_send_heartbeat(
                "[Janpara] iPad heartbeat (degraded run)",
                "Janpara iPad watcher completed with degraded status: all feeds failed or returned busy pages.",
            )
        else:
            logging.info("No new items or price drops")
            maybe_send_heartbeat(
                "[Janpara] iPad heartbeat (no changes)",
                "Janpara iPad watcher is healthy. No new items or price drops in recent runs.",
            )

    save_state(state)

if __name__ == "__main__":
    main()
