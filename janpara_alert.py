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
from bs4 import BeautifulSoup
from dotenv import load_dotenv

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

# Always request "newest first"
SORT_ORDER = "4"         # Janpara ORDER=4 → newest
MAX_PAGES = 8            # fewer pages needed with newest-first
REQUEST_DELAY_SEC = 1.3
HTTP_TIMEOUT_SEC = 20
REQUIRE_PRICE = True
ONLY_SMARTPHONE_DETAIL = True

# HTTP / pacing / retries
MAX_RETRIES = 5
BACKOFF_BASE = 1.8
JITTER_RATIO = 0.20
RETRY_STATUS = {429, 500, 502, 503, 504}

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) JanparaWatcher/2.3",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "ja,en;q=0.9",
    "Cache-Control": "no-cache",
    "Pragma": "no-cache",
    "Connection": "keep-alive",
    "Referer": "https://www.janpara.co.jp/",
}

STATE_FILE = (HERE / "state" / "janpara_seen.json")
STATE_FILE.parent.mkdir(parents=True, exist_ok=True)

# Feeds with first-page URLs + brand-specific pagination rules
FEEDS = [
    {
        "name": "Xiaomi Smartphones",
        "url": "https://www.janpara.co.jp/sale/search/result/?cache_key=/sale/search/result/&OUTCLSCODE=46&PRBFLTWORD01_FILTER%5B0%5D=5&PAGE=1",
        "must_include": ["xiaomi", "redmi", "mi "],  # "mi " avoids matching "sim"
        "must_not_include": ["ipad", "pad ", "case", "cover", "cable", "watch", "band", "earbuds", "buds"],
        "paginate": True,
        "pagination": {"param": "PAGE", "cache_key": "/sale/search/result/", "require_page1": True},
    },
    {
        "name": "Google Smartphones",
        "url": "https://www.janpara.co.jp/sale/search/result/?cache_key=/sale/search/result/&OUTCLSCODE=46&PRBFLTWORD01_FILTER%5B0%5D=0&PAGE=1",
        "must_include": ["google", "pixel"],
        "must_not_include": ["ipad", "case", "cover", "watch", "band", "buds", "earbuds"],
        "paginate": True,
        "pagination": {"param": "PAGE", "cache_key": "/sale/search/result/", "require_page1": True},
    },
    {
        "name": "OnePlus Smartphones",
        "url": "https://www.janpara.co.jp/sale/search/result/?SSHPCODE=&OUTCLSCODE=46&KEYWORDS=oneplus&x=0&y=0&CHKOUTCOM=1",
        "variants": [
            "https://www.janpara.co.jp/sale/search/result/?SSHPCODE=&OUTCLSCODE=46&KEYWORDS=Nord&x=0&y=0&CHKOUTCOM=1",
            "https://www.janpara.co.jp/sale/search/result/?SSHPCODE=&OUTCLSCODE=46&KEYWORDS=%E3%83%AF%E3%83%B3%E3%83%97%E3%83%A9%E3%82%B9&x=0&y=0&CHKOUTCOM=1",  # ワンプラス
        ],
        "must_include": ["oneplus", "nord", "ワンプラス"],
        "must_not_include": ["case", "cover", "watch", "band", "buds", "earbuds"],
        "paginate": True,
        "pagination": {"param": "PAGE", "cache_key": "/sale/search/result/", "require_page1": False},
    },
]

# Busy-page detection (content strings)
BUSY_PHRASES = [
    "アクセス集中により大変混み合っております。",
    "しばらく時間をおいてから再度お越し下さい",
    "Service Temporarily Unavailable",
    "503",
]

# --- Dedup strategy: URL + price + stock ---
# A new price or an increased stock count at the same URL will trigger a new alert.
DEDUP_MODE = "url_price_stock"

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
    """Prefer Used(中古) price; else min among labeled; else min overall. Returns '¥xx,xxx' or ''."""
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

def ascii_price(p: str) -> str:
    """'¥13,980' / '13,980円' → '13,980 JPY'."""
    if not p:
        return p
    y = p.replace("円", "").replace("¥", "").strip()
    return f"{y} JPY"

def price_to_int(price_str: str) -> int:
    """Convert '13,980 JPY' (or similar) back to 13980 for dedup keys."""
    if not price_str:
        return 0
    m = re.search(r"(\d{1,3}(?:,\d{3})+)", price_str)
    return int(m.group(1).replace(",", "")) if m else 0

# =========================
# ATTRIBUTE HELPERS (color, condition, stock)
# =========================
COLOR_MAP = {
    # English
    "black": "Black", "white": "White", "blue": "Blue", "green": "Green",
    "red": "Red", "purple": "Purple", "pink": "Pink", "silver": "Silver",
    "gold": "Gold", "gray": "Gray", "grey": "Gray", "titanium": "Titanium",
    "chrome": "Chrome", "midnight": "Midnight", "starlight": "Starlight",
    # Japanese katakana
    "ブラック": "Black", "ホワイト": "White", "ブルー": "Blue", "グリーン": "Green",
    "レッド": "Red", "パープル": "Purple", "ピンク": "Pink", "シルバー": "Silver",
    "ゴールド": "Gold", "グレー": "Gray", "グレイ": "Gray",
    "ナイトフォール": "Nightfall", "ミッドナイト": "Midnight", "チタニウム": "Titanium",
    "クローム": "Chrome",
}

def extract_color(text: str) -> str | None:
    t = text
    for raw, canon in sorted(COLOR_MAP.items(), key=lambda kv: -len(kv[0])):
        if raw.lower() in t.lower():
            return canon
    return None

COND_RE = re.compile(r"(未使用|新品|中古\s*[SABC]?)", re.IGNORECASE)
def extract_condition(text: str) -> str | None:
    m = COND_RE.search(text)
    if not m:
        return None
    token = m.group(1)
    token = token.replace(" ", "")
    if token.startswith(("未使用", "新品")):
        return "Unused"
    if token.startswith("中古"):
        g = re.search(r"中古\s*([SABC])", token, re.IGNORECASE)
        return f"Used{(' ' + g.group(1)) if g else ''}"
    return None

STOCK_RE = re.compile(r"(\d+)\s*個の?在庫|在庫\s*(\d+)\s*個")
def extract_stock_count(text: str) -> int | None:
    m = STOCK_RE.search(text)
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
    if STATE_FILE.exists():
        try:
            state = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        except Exception:
            state = {}
    else:
        state = {}

    # migrate relative → absolute (old schema list[str]) AND keep as-is for new dict schema
    changed = False
    new_state = {}
    for feed, entry in list(state.items()):
        # entry can be list[str] (old) or {"keys": [...] } (new)
        if isinstance(entry, list):
            # upgrade each to absolute url when possible (best-effort)
            upgraded = []
            for u in entry:
                upgraded.append(u if u.startswith("http") else urljoin(BASE_URL, u))
            new_state[feed] = {"keys": sorted(set(upgraded))}
            changed = True
        elif isinstance(entry, dict) and isinstance(entry.get("keys"), list):
            # keep as-is
            new_state[feed] = entry
        else:
            new_state[feed] = {"keys": []}
            changed = True

    if changed:
        save_state(new_state)
        logging.info("State migration: upgraded to dict schema and absolute URLs.")
    return new_state if changed else state

def save_state(state):
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")

def is_detail_link(href: str) -> bool:
    if not href:
        return False
    hl = href.lower()
    ok = ("/sale/detail" in hl) or ("/sale/stockdetail" in hl) or ("/sale/" in hl and "detail" in hl)
    return ok if ONLY_SMARTPHONE_DETAIL else ("/sale/" in hl)

def normalize_url(url: str) -> str:
    return urljoin(BASE_URL, url)

def clean_text(text: str) -> str:
    if not text:
        return ""
    text = unicodedata.normalize("NFKC", text)   # collapse full-width forms
    return re.sub(r"\s+", " ", text).strip()

# --- retry / backoff + busy-page detection ---
def _sleep_with_jitter(base: float, attempt: int):
    wait = base ** (attempt - 1)
    jitter = wait * random.uniform(-JITTER_RATIO, JITTER_RATIO)
    time.sleep(max(0.5, wait + jitter))

def is_busy_response(resp: requests.Response) -> bool:
    if resp.status_code in RETRY_STATUS:
        return True
    try:
        text = resp.text[:2000]
    except Exception:
        return False
    return any(p in text for p in BUSY_PHRASES)

def request_get_with_retries(url: str, headers: dict, timeout: int) -> requests.Response:
    last_exc = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            r = requests.get(url, headers=headers, timeout=timeout)
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
    return parse_listing_cards(soup)

def parse_listing_cards(soup: BeautifulSoup):
    """Return list of {id, title, price, store, href, color, condition, stock} parsed from product cards."""
    items = {}
    brand_keywords = ["Xiaomi", "Redmi", "Mi ", "Google", "Pixel", "OnePlus", "Nord", "ワンプラス", "Galaxy", "iPhone", "Xperia", "AQUOS"]

    for a in soup.find_all("a", href=True):
        href = a["href"]
        if not is_detail_link(href):
            continue

        full = normalize_url(href)
        uid = full

        # Find a reasonable container (walk up a few levels)
        container = a
        for _ in range(4):
            container = container.parent
            if container is None:
                break
            if hasattr(container, "get_text") and len(list(container.descendants)) > 20:
                break

        block_text = container.get_text(" ", strip=True) if container else a.get_text(" ", strip=True)

        # Title candidates
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

        # Prices (prefer Used; else lowest)
        price_list = extract_prices_with_labels(block_text)
        price_raw = choose_best_price(price_list)
        if REQUIRE_PRICE and not price_raw:
            continue

        # Store (Japanese "店")
        store = ""
        m = re.search(r"(\S+店)", block_text)
        if m:
            store = clean_text(m.group(1))

        # Enriched attributes
        color = extract_color(chosen_title) or extract_color(block_text) or ""
        condition = extract_condition(block_text) or ""
        stock = extract_stock_count(block_text)  # int or None

        items[uid] = {
            "id": uid,
            "title": chosen_title,
            "price": ascii_price(price_raw),
            "store": store,
            "href": full,
            "color": color,
            "condition": condition,
            "stock": stock if stock is not None else 0,
        }

    return list(items.values())

# --- URL query manipulation & pagination ---
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
    """
    Brand-specific pagination + enforce newest-first:
      - Xiaomi/Google: page 1 includes cache_key & PAGE=1
      - OnePlus: page 1 keeps base; add cache_key & PAGE for page>=2
      - Always inject ORDER=4
    """
    base_url = feed["url"]
    pg = feed.get("pagination", {})
    page_param = pg.get("param", "PAGE")
    cache_key_val = pg.get("cache_key", "/sale/search/result/")
    require_page1 = pg.get("require_page1", False)

    if page == 1:
        if require_page1:
            return _with_params(base_url, **{page_param: "1", "cache_key": cache_key_val, "ORDER": SORT_ORDER})
        else:
            return _with_params(base_url, ORDER=SORT_ORDER)

    return _with_params(base_url, **{page_param: str(page), "cache_key": cache_key_val, "ORDER": SORT_ORDER})

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
        # polite delay (with jitter)
        time.sleep(max(0.5, REQUEST_DELAY_SEC * random.uniform(1 - JITTER_RATIO, 1 + JITTER_RATIO)))
    return all_items

def fetch_all_pages_for_url(url: str, pagination: dict | None, max_pages: int) -> list:
    """Page through a single URL using the same pagination rules as the parent feed."""
    dummy_feed = {"url": url, "pagination": pagination or {}}
    return fetch_feed_all_pages(dummy_feed, max_pages=max_pages)

def filter_items_by_brand(items, must_include=None, must_not_include=None):
    mi = [m.lower() for m in (must_include or [])]
    mn = [m.lower() for m in (must_not_include or [])]
    filtered = []
    for it in items:
        title = (it.get("title", "") or "").lower()
        if mi and not any(w in title for w in mi):
            continue
        if mn and any(w in title for w in mn):
            continue
        filtered.append(it)
    return filtered

# --- Dedup key: URL + price + stock ---
def build_item_key(item: dict) -> str:
    price_i = price_to_int(item.get("price"))
    stock = item.get("stock") or 0
    return f"{item.get('href','')}|p{price_i}|q{stock}"

def diff_new_items(feed_name: str, current_items: list, state: dict):
    """
    New schema:
      state[feed_name] = {"keys": ["<dedup_key>", ...]}
    Old schemas auto-migrate to new dict + absolute URLs in load_state().
    """
    feed_state = state.get(feed_name)
    if isinstance(feed_state, dict) and isinstance(feed_state.get("keys"), list):
        seen_keys = set(feed_state["keys"])
    elif isinstance(feed_state, list):
        # very old: treat as seen keys directly
        seen_keys = set(feed_state)
    else:
        seen_keys = set()

    new_items = []
    for it in current_items:
        key = build_item_key(it)
        if key not in seen_keys:
            new_items.append(it)
            seen_keys.add(key)

    state[feed_name] = {"keys": sorted(seen_keys)}
    return new_items, state

def format_email_body(all_new):
    lines = []
    lines.append("New smartphone listings found on Janpara\n")
    for feed_name, new_items in all_new:
        if not new_items:
            continue

        # --- sort items by price ascending ---
        def sort_key(it):
            return price_to_int(it.get("price", "")) or 0

        sorted_items = sorted(new_items, key=sort_key)

        lines.append(f"=== {feed_name} ===")
        for it in sorted_items:
            lines.append(f"- {it['title']}")
            if it.get("price"):
                lines.append(f"  Price: {it['price']}")
            if it.get("color"):
                lines.append(f"  Color: {it['color']}")
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
    msg["Subject"] = "[Janpara] New smartphone listings"
    msg["From"] = from_email
    msg["To"] = ", ".join(to_emails)
    msg["Date"] = formatdate(localtime=True)
    with smtplib.SMTP(smtp_host, smtp_port, timeout=30) as s:
        s.ehlo(); s.starttls(); s.login(smtp_user, smtp_pass); s.sendmail(from_email, to_emails, msg.as_string())

# =========================
# MAIN
# =========================
def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    state = load_state()
    all_new = []
    any_success = False

    for feed in FEEDS:
        name = feed["name"]
        logging.info("Fetching: %s", name)
        items = []

        # 1) Base URL (paginate if configured)
        try:
            if feed.get("paginate", False):
                items.extend(fetch_feed_all_pages(feed, max_pages=MAX_PAGES))
            else:
                items.extend(fetch_and_parse(feed["url"]))
            any_success = any_success or bool(items)
        except Exception as e:
            logging.warning("%s: base URL failed (%s). Will try variants if any.", name, e)

        # 2) Variants (e.g., OnePlus 'Nord', 'ワンプラス')
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

        # Deduplicate by absolute href/ID (before brand filter)
        dedup, seen = [], set()
        for it in items:
            if it["id"] in seen:
                continue
            seen.add(it["id"])
            dedup.append(it)
        items = dedup

        # Brand filter (relax for OnePlus if empty but items exist)
        filtered = filter_items_by_brand(items, feed.get("must_include"), feed.get("must_not_include"))
        if not filtered and "OnePlus" in name and items:
            logging.warning("OnePlus: 0 after brand filter; relaxing filter for visibility this run.")
            filtered = items

        logging.info("%s: %d items after brand filter", name, len(filtered))

        # (Optional) peek at dedup keys
        if filtered[:3]:
            sample_keys = [build_item_key(it) for it in filtered[:3]]
            logging.debug("%s: sample dedup keys: %s", name, sample_keys)

        new_items, state = diff_new_items(name, filtered, state)
        logging.info("%s: new %d", name, len(new_items))
        if new_items:
            all_new.append((name, new_items))

        time.sleep(max(0.5, REQUEST_DELAY_SEC * random.uniform(1 - JITTER_RATIO, 1 + JITTER_RATIO)))

    if all_new:
        body = format_email_body(all_new)
        send_email("[Janpara] New smartphone listings", body)
        logging.info("Email sent with %d feed groups", len(all_new))
    else:
        if not any_success:
            logging.warning("Run degraded: all feeds failed or returned busy pages.")
            # Optional: notify on full failure
            # send_email("[Janpara] Alert run degraded", "Janpara returned busy pages (503). No new items this run.")
        else:
            logging.info("No new items")

    save_state(state)

if __name__ == "__main__":
    main()