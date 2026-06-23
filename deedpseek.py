#!/usr/bin/env python3
"""
Stream resolver - extracts embed URLs from streamingnow.mov.

Strategy:
  1. Direct HTTP (no proxy) — works on non-blocked IPs (local machine).
  2. Proxy rotation — tries each proxy in PROXY_LIST until one works (CI/datacenter IPs).
  3. nodriver fallback — headed Chrome via Xvfb if all HTTP paths fail.

Requires:
    pip install requests nodriver

Run:
    python deedpseek.py "https://multiembed.mov/?video_id=1339713&tmdb=1"
"""

from __future__ import annotations

import argparse
import asyncio
import html
import json
import os
import re
import shutil
import sys
import tempfile
import time
import traceback
import urllib.parse
from dataclasses import asdict, dataclass, field
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any, Dict, Iterable, List, Optional

import requests

DEFAULT_INPUT_URL = "https://multiembed.mov/?video_id=1339713&tmdb=1"
IS_CI = os.environ.get("CI", "false").lower() == "true"

PAGE_LOAD_WAIT   = 12
XHR_WAIT         = 10
PLAYVIDEO_WAIT   = 10
MAX_SERVER_PAGES = 10

# Tried in order; first one that gets a real response wins.
# US proxy is first — least likely to be geo-blocked by the target.
_PROXY_USER = "iooshumq"
_PROXY_PASS = "8x072nppng86"

def _px(host: str, port: str) -> str:
    return f"http://{_PROXY_USER}:{_PROXY_PASS}@{host}:{port}"

# Authenticated residential proxies — US/UK first (least likely to be geo-blocked)
PROXY_LIST = [
    _px("38.154.203.95",  "5863"),   # US – Piscataway
    _px("198.23.243.226", "6361"),   # US – Los Angeles
    _px("38.154.185.97",  "6370"),   # US – Piscataway
    _px("191.96.254.138", "6185"),   # US – Los Angeles
    _px("31.56.127.193",  "7684"),   # US – Seattle
    _px("31.59.20.176",   "6754"),   # UK – London
    _px("45.38.107.97",   "6014"),   # UK – London
    _px("198.105.121.200","6462"),   # UK – London
    _px("64.137.96.74",   "6641"),   # ES – Madrid
    _px("142.111.67.146", "5611"),   # JP – Tokyo
]

# ── Regex ──────────────────────────────────────────────────────────────────
PLAY_TOKEN_RE    = re.compile(r"""[?&]play=([^&"'<>]+)""", re.IGNORECASE)
LOAD_SOURCES_RE  = re.compile(r"""load_sources\((['"])(?P<token>[^'"]+)\1\)""")
IFRAME_SRC_RE    = re.compile(r"""<iframe\b[^>]*\bsrc\s*=\s*(['"])(?P<src>.*?)\1""", re.IGNORECASE | re.DOTALL)
SOURCE_LI_RE     = re.compile(r"""<li\b(?P<attrs>[^>]*\bdata-id=[^>]*)>""", re.IGNORECASE | re.DOTALL)
ATTR_RE          = re.compile(r"""([:\w-]+)\s*=\s*(['"])(.*?)\2""", re.DOTALL)
DATA_SRC_RE      = re.compile(r"""data-src\s*=\s*['"]([^'"]+)['"]""", re.IGNORECASE)
SOURCE_FRAME_RE  = re.compile(r"""source-frame[^>]*src\s*=\s*['"]([^'"]+)['"]""", re.IGNORECASE)
JS_IFRAME_SRC_RE = re.compile(r"""['"]src['"]\s*:\s*['"]([^'"]+)['"]""", re.IGNORECASE)
JS_SRC_ASSIGN_RE = re.compile(r"""\.src\s*=\s*['"]([^'"]*/(?:e|embed|d)/[^'"]+)['"]""", re.IGNORECASE)
ANY_URL_RE       = re.compile(r'https?://[^\s"\'<>]+', re.IGNORECASE)

CF_MARKERS = [
    "challenges.cloudflare.com",
    "cf-browser-verification",
    "cf_clearance",
    "Just a moment",
    "Enable JavaScript and cookies to continue",
    "Checking your browser",
]

BROWSER_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/125.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
    "Accept-Encoding": "gzip, deflate, br",
    "DNT": "1",
    "Connection": "keep-alive",
    "Upgrade-Insecure-Requests": "1",
    "Sec-Fetch-Dest": "document",
    "Sec-Fetch-Mode": "navigate",
    "Sec-Fetch-Site": "none",
    "Sec-Fetch-User": "?1",
    "Cache-Control": "max-age=0",
}


# ── Data classes ───────────────────────────────────────────────────────────

@dataclass
class SourceChoice:
    video_id: str
    server_id: str
    label: str = ""
    quality: str = ""


@dataclass
class ResolveResult:
    input_url: str
    ok: bool
    status: str
    play_url: Optional[str] = None
    play_token: Optional[str] = None
    sources: List[SourceChoice] = field(default_factory=list)
    embed_urls: List[str] = field(default_factory=list)
    stream_urls: List[str] = field(default_factory=list)
    steps: List[str] = field(default_factory=list)
    errors: List[str] = field(default_factory=list)
    stats: Dict[str, Any] = field(default_factory=dict)
    used_live_http: bool = False
    used_nodriver: bool = False
    cf_bypass_method: str = ""

    def to_jsonable(self) -> Dict[str, Any]:
        data = asdict(self)
        data["sources"] = [asdict(s) for s in self.sources]
        return data


# ── Helpers ────────────────────────────────────────────────────────────────

def unique_keep_order(items: Iterable[str]) -> List[str]:
    seen, out = set(), []
    for item in items:
        if item and item not in seen:
            seen.add(item)
            out.append(item)
    return out


def is_valid_embed_url(url: str) -> bool:
    if not url or not url.startswith("http"):
        return False
    skip = [
        '.js', '.css', '.png', '.jpg', '.svg', '.ico', '.woff', '.gif',
        'googleapis', 'cloudflare', 'gstatic', 'google.com',
        'earn-money', 'api-docs', 'help.', 'example.com',
        '&quot;', '&lt;', '&gt;', '&amp;',
        'cdnjs', 'jsdelivr', 'pagead', 'googlesyndication',
        'facebook.com', 'twitter.com', 'instagram.com',
        'jquery', 'bootstrap', 'fontawesome',
    ]
    embed = [
        '/e/', '/embed', '/d/', '/v/',
        'vipstream', 'mixdrop', 'vidmoly',
        'streamwish', 'streamhls', 'dsvplay',
        'voe.sx', 'dood', 'playmogo',
        'streamtape', 'netu', 'filelions',
        'movearnpre',
    ]
    url_lower = url.lower()
    if any(p in url_lower for p in skip):
        return False
    return any(p in url_lower for p in embed)


def clean_text(fragment: str) -> str:
    fragment = re.sub(r"<script\b.*?</script>", " ", fragment, flags=re.IGNORECASE | re.DOTALL)
    fragment = re.sub(r"<style\b.*?</style>",   " ", fragment, flags=re.IGNORECASE | re.DOTALL)
    fragment = re.sub(r"<[^>]+>", " ", fragment)
    return " ".join(html.unescape(fragment).split())


def attrs_to_dict(raw_attrs: str) -> Dict[str, str]:
    return {name.lower(): html.unescape(value) for name, _, value in ATTR_RE.findall(raw_attrs)}


def extract_play_token(text: str) -> Optional[str]:
    m = PLAY_TOKEN_RE.search(text)
    if m:
        return urllib.parse.unquote(m.group(1))
    m = LOAD_SOURCES_RE.search(text)
    if m:
        return m.group("token")
    return None


def extract_source_choices(response_html: str) -> List[SourceChoice]:
    sources = []
    matches = list(SOURCE_LI_RE.finditer(response_html))
    for i, match in enumerate(matches):
        attrs = attrs_to_dict(match.group("attrs"))
        video_id  = attrs.get("data-id")
        server_id = attrs.get("data-server")
        if not video_id or not server_id:
            continue
        end = matches[i + 1].start() if i + 1 < len(matches) else response_html.find("</ul>", match.end())
        if end < 0:
            end = min(len(response_html), match.end() + 500)
        fragment = response_html[match.end():end]
        qm = re.search(r"""<span\b[^>]*class=(['"])[^'"]*\bquality\b[^'"]*\1[^>]*>(.*?)</span>""",
                        fragment, re.I | re.S)
        quality = clean_text(qm.group(2)) if qm else ""
        label   = clean_text(fragment)
        sources.append(SourceChoice(video_id=video_id, server_id=server_id, label=label, quality=quality))
    return sources


def extract_embed_urls_from_html(html_content: str, base_url: str) -> List[str]:
    urls = []
    for m in IFRAME_SRC_RE.finditer(html_content):
        src = html.unescape(m.group("src")).strip()
        full = urllib.parse.urljoin(base_url, src)
        if is_valid_embed_url(full):
            urls.append(full)
    for m in SOURCE_FRAME_RE.finditer(html_content):
        src = m.group(1).strip()
        full = urllib.parse.urljoin(base_url, src)
        if is_valid_embed_url(full):
            urls.append(full)
    for m in DATA_SRC_RE.finditer(html_content):
        src = m.group(1).strip()
        full = urllib.parse.urljoin(base_url, src)
        if is_valid_embed_url(full):
            urls.append(full)
    for m in JS_IFRAME_SRC_RE.finditer(html_content):
        src = m.group(1).strip()
        if src.startswith("http") and is_valid_embed_url(src):
            urls.append(src)
        elif src.startswith("//") and is_valid_embed_url("https:" + src):
            urls.append("https:" + src)
    for m in JS_SRC_ASSIGN_RE.finditer(html_content):
        src = m.group(1).strip()
        if src.startswith("http") and is_valid_embed_url(src):
            urls.append(src)
        elif src.startswith("/"):
            full = urllib.parse.urljoin(base_url, src)
            if is_valid_embed_url(full):
                urls.append(full)
    for url in ANY_URL_RE.findall(html_content):
        url = url.rstrip('.,;:)!]}\'"')
        if is_valid_embed_url(url) and url not in urls:
            urls.append(url)
    return unique_keep_order(urls)


def is_cf_blocked(text: str) -> bool:
    return any(m in text for m in CF_MARKERS)


def is_hard_blocked(status_code: int, text: str) -> bool:
    """True if the server is flat-out refusing us (IP block or CF)."""
    return status_code in (403, 407, 429) or is_cf_blocked(text)


# ── HTTP session builder ───────────────────────────────────────────────────

def make_session(proxy: Optional[str] = None) -> requests.Session:
    s = requests.Session()
    s.headers.update(BROWSER_HEADERS)
    s.max_redirects = 10
    if proxy:
        s.proxies = {"http": proxy, "https": proxy}
    return s


def probe_proxy(proxy: str, test_url: str, timeout: int = 12) -> bool:
    """Return True if this proxy can reach test_url and get a real page (not 403/CF)."""
    try:
        s = make_session(proxy)
        r = s.get(test_url, timeout=timeout, allow_redirects=True)
        if is_hard_blocked(r.status_code, r.text):
            return False
        return True
    except Exception:
        return False


def find_working_proxy(test_url: str, steps: List[str]) -> Optional[str]:
    """
    Probe each proxy in PROXY_LIST against test_url.
    Returns the first proxy that gets a real response, or None.
    """
    steps.append(f"  Probing {len(PROXY_LIST)} proxies against {test_url[:50]}...")
    for proxy in PROXY_LIST:
        steps.append(f"    Trying proxy {proxy} ...")
        if probe_proxy(proxy, test_url):
            steps.append(f"    ✓ Proxy works: {proxy}")
            return proxy
        steps.append(f"    ✗ Proxy failed: {proxy}")
    return None


# ── Core HTTP fetch logic (shared by direct + proxy paths) ────────────────

def http_resolve_with_session(
    sess: requests.Session,
    input_url: str,
    preferred_server: Optional[str],
    all_servers: bool,
    result: ResolveResult,
    step_offset: int = 0,
) -> bool:
    """
    Run the full HTTP resolve flow using `sess`.
    Populates result in-place. Returns True if embed URLs were found.
    step_offset shifts the step numbers so proxy attempts don't clash.
    """
    n = step_offset
    total_requests = 0

    # Step 1: initial GET
    resp = sess.get(input_url, timeout=30, allow_redirects=False)
    total_requests += 1
    result.steps.append(f"{n+1}. Initial GET: HTTP {resp.status_code}")

    if resp.status_code in (301, 302, 303, 307, 308):
        location = resp.headers.get("Location", "")
        result.steps.append(f"{n+2}. Redirect → {urllib.parse.urlparse(location).netloc}")
        play_url = location
    elif resp.status_code == 200:
        play_url = resp.url
        result.steps.append(f"{n+2}. No redirect, URL: {play_url[:80]}")
    else:
        result.errors.append(f"Initial GET returned HTTP {resp.status_code}")
        return False

    result.play_token = extract_play_token(play_url)
    result.play_url   = play_url

    # Step 3: GET play page
    sess.headers.update({"Referer": input_url})
    play_resp = sess.get(play_url, timeout=30)
    total_requests += 1
    play_html = play_resp.text
    result.steps.append(f"{n+3}. Play page: HTTP {play_resp.status_code}, {len(play_html)} bytes")

    if is_hard_blocked(play_resp.status_code, play_html):
        result.errors.append(f"Play page blocked: HTTP {play_resp.status_code}")
        return False

    if not result.play_token:
        result.play_token = extract_play_token(play_html)
    if not result.play_token:
        result.errors.append("No play token found")
        return False

    # Step 4: POST to response.php
    response_php_url = urllib.parse.urljoin(play_resp.url, "/response.php")
    sess.headers.update({
        "Referer":          play_resp.url,
        "X-Requested-With": "XMLHttpRequest",
        "Content-Type":     "application/x-www-form-urlencoded",
        "Sec-Fetch-Dest":   "empty",
        "Sec-Fetch-Mode":   "cors",
        "Sec-Fetch-Site":   "same-origin",
    })
    rphp = sess.post(response_php_url, data={"token": result.play_token}, timeout=30)
    total_requests += 1
    result.steps.append(f"{n+4}. response.php: HTTP {rphp.status_code}, {len(rphp.text)} bytes")

    if is_hard_blocked(rphp.status_code, rphp.text):
        result.errors.append(f"response.php blocked: HTTP {rphp.status_code}")
        return False

    result.sources = extract_source_choices(rphp.text)
    result.steps.append(f"{n+5}. Found {len(result.sources)} source(s)")
    if not result.sources:
        result.errors.append("No sources found in response.php")
        return False

    # Pick servers
    if all_servers:
        sources_to_try = result.sources[:MAX_SERVER_PAGES]
    elif preferred_server:
        sources_to_try = [s for s in result.sources if s.server_id == preferred_server] or result.sources[:1]
    else:
        priority = ["21", "89", "90", "88", "29", "12", "41", "50", "45", "34", "38"]
        ordered  = sorted(result.sources, key=lambda s: priority.index(s.server_id) if s.server_id in priority else 99)
        sources_to_try = ordered[:MAX_SERVER_PAGES]

    result.steps.append(f"{n+6}. Processing {len(sources_to_try)} server(s)")

    # Reset to document headers for playvideo.php
    sess.headers.update({
        "Sec-Fetch-Dest": "document",
        "Sec-Fetch-Mode": "navigate",
        "Sec-Fetch-Site": "same-origin",
    })
    if "Content-Type" in sess.headers:
        del sess.headers["Content-Type"]

    for source in sources_to_try:
        playvideo_url = (
            urllib.parse.urljoin(play_resp.url, "/playvideo.php")
            + f"?video_id={urllib.parse.quote(source.video_id)}"
            + f"&server_id={urllib.parse.quote(source.server_id)}"
            + f"&token={urllib.parse.quote(result.play_token)}&init=1"
        )
        result.steps.append(f"  Server {source.server_id}: {source.label[:50]}")
        sess.headers.update({"Referer": play_resp.url})

        for attempt in range(1, 3):
            try:
                pv = sess.get(playvideo_url, timeout=30)
                total_requests += 1
                pv_html = pv.text
                result.steps.append(f"    attempt {attempt}: HTTP {pv.status_code}, {len(pv_html)} bytes")
                if is_hard_blocked(pv.status_code, pv_html):
                    result.steps.append(f"    blocked — skipping server")
                    break
                found = extract_embed_urls_from_html(pv_html, pv.url)
                result.steps.append(f"    Found {len(found)} embed URL(s)")
                for eu in found:
                    result.steps.append(f"      → {eu[:80]}")
                    if eu not in result.embed_urls:
                        result.embed_urls.append(eu)
                break
            except requests.RequestException as exc:
                result.steps.append(f"    attempt {attempt} error: {exc}")
                time.sleep(1)

    result.stats["total_requests"] = result.stats.get("total_requests", 0) + total_requests
    return bool(result.embed_urls)


# ── Pure-HTTP resolver (direct then proxy) ────────────────────────────────

def resolve_with_http(
    input_url: str,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    result = ResolveResult(input_url=input_url, ok=False, status="http")
    started = time.time()
    result.stats["total_requests"] = 0

    # ── Attempt 1: direct (no proxy) ──────────────────────────────────────
    result.steps.append("── Direct HTTP (no proxy) ──")
    try:
        sess = make_session()
        ok = http_resolve_with_session(sess, input_url, preferred_server, all_servers, result, step_offset=0)
    except Exception as exc:
        ok = False
        result.errors.append(f"Direct HTTP error: {exc}")

    if ok:
        result.used_live_http   = True
        result.cf_bypass_method = "live_http_direct"
        _finalize_http(result, started)
        return result

    # ── Attempt 2: proxy rotation ──────────────────────────────────────────
    result.steps.append("── Direct failed — trying proxy rotation ──")
    # Use the play redirect URL as probe target if we have it, else use the input host
    probe_target = result.play_url or f"https://{urllib.parse.urlparse(input_url).netloc}/"
    proxy = find_working_proxy(probe_target, result.steps)

    if proxy:
        result.steps.append(f"── Running full resolve via proxy {proxy} ──")
        # Reset state for a fresh attempt through the proxy
        result.sources   = []
        result.embed_urls = []
        result.play_url  = None
        result.play_token = None
        try:
            sess = make_session(proxy)
            ok = http_resolve_with_session(sess, input_url, preferred_server, all_servers, result, step_offset=10)
        except Exception as exc:
            ok = False
            result.errors.append(f"Proxy HTTP error: {exc}")

        if ok:
            result.used_live_http   = True
            result.cf_bypass_method = f"live_http_proxy:{proxy}"
            _finalize_http(result, started)
            return result

    result.errors.append("All HTTP paths failed (direct + all proxies)")
    result.status = "http_failed"
    _finalize_http(result, started)
    return result


def _finalize_http(result: ResolveResult, started: float):
    elapsed = round(time.time() - started, 1)
    result.embed_urls = unique_keep_order([u for u in result.embed_urls if u and u != "https://"])
    result.ok   = bool(result.embed_urls)
    if result.ok:
        result.steps.append(f"✓ SUCCESS: {len(result.embed_urls)} embed URL(s) in {elapsed}s")
        result.status = "ok"
    result.stats.update({
        "elapsed_seconds":     elapsed,
        "requests_per_second": round(result.stats.get("total_requests", 0) / elapsed, 2) if elapsed else 0,
        "sources_found":       len(result.sources),
        "embed_urls_found":    len(result.embed_urls),
    })


# ── CDP network interception ───────────────────────────────────────────────

async def enable_network_and_intercept(page, captured_responses: dict):
    import nodriver.cdp.network as cdp_network
    await page.send(cdp_network.enable())

    async def on_response_received(event):
        url = event.response.url
        if "response.php" in url or "playvideo.php" in url:
            try:
                body, _ = await page.send(cdp_network.get_response_body(event.request_id))
                for key in ("response.php", "playvideo.php"):
                    if key in url:
                        captured_responses.setdefault(key, []).append({"url": url, "body": body})
            except Exception:
                pass

    page.add_handler(cdp_network.ResponseReceived, on_response_received)


# ── nodriver fallback ──────────────────────────────────────────────────────

async def resolve_with_nodriver(
    input_url: str,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    import nodriver as uc

    result = ResolveResult(input_url=input_url, ok=False, status="nodriver")
    started = time.time()
    sources_to_try: List[SourceChoice] = []

    chrome_bin = (
        shutil.which("google-chrome") or shutil.which("google-chrome-stable")
        or shutil.which("chromium-browser") or shutil.which("chromium")
        or "/usr/bin/google-chrome"
    )
    user_data_dir = tempfile.mkdtemp(prefix="nodriver_")
    browser = None

    try:
        browser = await uc.start(
            headless=False,
            browser_executable_path=chrome_bin,
            user_data_dir=user_data_dir,
            browser_args=[
                "--no-sandbox", "--disable-dev-shm-usage",
                "--disable-gpu", "--window-size=1280,900",
            ],
        )

        captured = {}
        page = await browser.get(input_url)
        await enable_network_and_intercept(page, captured)
        result.steps.append("1. CDP network interception enabled")
        await page.sleep(PAGE_LOAD_WAIT)

        current_url = await page.evaluate("window.location.href")
        result.play_url   = current_url
        result.play_token = extract_play_token(current_url)
        result.steps.append(f"2. URL: {current_url[:80]}")
        result.steps.append(f"   token={'yes' if result.play_token else 'no'}")

        for _ in range(XHR_WAIT):
            if "response.php" in captured:
                break
            await page.sleep(1)

        if "response.php" in captured:
            body = captured["response.php"][0]["body"]
            result.steps.append(f"3. Intercepted response.php ({len(body)} bytes)")
            result.sources = extract_source_choices(body)
            result.steps.append(f"   Sources from XHR: {len(result.sources)}")
        else:
            result.steps.append("3. response.php not intercepted — trying page HTML")
            page_html = await page.get_content()
            result.sources = extract_source_choices(page_html)
            result.steps.append(f"   Sources from page HTML: {len(result.sources)}")

        if not result.sources and result.play_token:
            result.steps.append("3b. Fetching response.php via JS...")
            response_url = urllib.parse.urljoin(current_url, "/response.php")
            js_result = await page.evaluate(f"""
                (async () => {{
                    try {{
                        const resp = await fetch('{response_url}', {{
                            method: 'POST',
                            headers: {{'Content-Type': 'application/x-www-form-urlencoded',
                                       'X-Requested-With': 'XMLHttpRequest'}},
                            body: 'token={urllib.parse.quote(result.play_token)}'
                        }});
                        return await resp.text();
                    }} catch(e) {{ return 'ERROR:' + e; }}
                }})()
            """)
            if js_result and not str(js_result).startswith("ERROR"):
                result.sources = extract_source_choices(str(js_result))
                result.steps.append(f"   Sources from JS fetch: {len(result.sources)}")
            else:
                page_html = await page.get_content()
                result.steps.append(f"   Page HTML snippet: {page_html[500:1500]}")

        if not result.play_token:
            result.errors.append("No play token found")
            return result
        if not result.sources:
            result.errors.append("No sources found after all attempts")
            return result

        if all_servers:
            sources_to_try = result.sources[:MAX_SERVER_PAGES]
        elif preferred_server:
            sources_to_try = [s for s in result.sources if s.server_id == preferred_server] or result.sources[:1]
        else:
            priority = ["21", "89", "90", "88", "29", "12", "41", "50", "45", "34", "38"]
            sources_to_try = sorted(result.sources,
                key=lambda s: priority.index(s.server_id) if s.server_id in priority else 99
            )[:MAX_SERVER_PAGES]

        result.steps.append(f"4. Processing {len(sources_to_try)} server(s)")

        for idx, source in enumerate(sources_to_try):
            playvideo_url = (
                urllib.parse.urljoin(result.play_url, "/playvideo.php")
                + f"?video_id={urllib.parse.quote(source.video_id)}"
                + f"&server_id={urllib.parse.quote(source.server_id)}"
                + f"&token={urllib.parse.quote(result.play_token)}&init=1"
            )
            result.steps.append(f"  [{idx+1}] Server {source.server_id}: {source.label[:40]}")
            try:
                pv_captured = {}
                pv_page = await browser.get(playvideo_url)
                await enable_network_and_intercept(pv_page, pv_captured)
                await pv_page.sleep(PLAYVIDEO_WAIT)

                pv_html    = await pv_page.get_content()
                pv_cur_url = await pv_page.evaluate("window.location.href")
                found = extract_embed_urls_from_html(pv_html, pv_cur_url)

                js_urls = await pv_page.evaluate("""
                    (() => {
                        const out = [];
                        document.querySelectorAll('iframe[src]').forEach(f => out.push(f.src));
                        document.querySelectorAll('[data-src]').forEach(f => out.push(f.dataset.src));
                        return out;
                    })()
                """)
                if js_urls:
                    for u in js_urls:
                        if u and is_valid_embed_url(u) and u not in found:
                            found.append(u)

                if "playvideo.php" in pv_captured:
                    for entry in pv_captured["playvideo.php"]:
                        for eu in extract_embed_urls_from_html(entry["body"], entry["url"]):
                            if eu not in found:
                                found.append(eu)

                result.steps.append(f"      → {len(found)} embed URL(s)")
                for eu in found:
                    if eu not in result.embed_urls:
                        result.embed_urls.append(eu)
                        result.steps.append(f"      ✓ {eu[:80]}")
            except Exception as exc:
                result.errors.append(f"Server {source.server_id}: {exc}")
                result.steps.append(f"      ✗ {exc}")

    except Exception as exc:
        result.errors.append(f"nodriver fatal: {type(exc).__name__}: {exc}")
        result.steps.append(f"FATAL: {traceback.format_exc()[-600:]}")
    finally:
        if browser:
            try:
                await browser.stop()
            except Exception:
                pass

    elapsed = round(time.time() - started, 1)
    result.embed_urls = unique_keep_order([u for u in result.embed_urls if u and u != "https://"])
    result.ok     = bool(result.embed_urls)
    result.status = "ok" if result.ok else "no_embeds"
    if result.ok:
        result.steps.append(f"✓ SUCCESS: {len(result.embed_urls)} embed URL(s) in {elapsed}s")
    result.stats = {
        "elapsed_seconds":   elapsed,
        "sources_found":     len(result.sources),
        "sources_processed": len(sources_to_try),
        "embed_urls_found":  len(result.embed_urls),
    }
    result.used_nodriver    = True
    result.cf_bypass_method = "nodriver"
    return result


# ── Top-level resolver ────────────────────────────────────────────────────

def resolve(
    input_url: str,
    *,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    # HTTP first (direct, then proxy rotation)
    result = resolve_with_http(input_url, preferred_server=preferred_server, all_servers=all_servers)
    if result.ok:
        return result

    # Last resort: nodriver (Chrome via Xvfb in CI)
    result.steps.append("→ All HTTP paths failed — falling back to nodriver (Chrome)")
    nd = asyncio.run(resolve_with_nodriver(input_url, preferred_server=preferred_server, all_servers=all_servers))
    nd.steps = result.steps + nd.steps
    return nd


# ── HTTP API ───────────────────────────────────────────────────────────────

class ApiHandler(BaseHTTPRequestHandler):
    server_version = "StreamResolver/12.0"

    def do_GET(self):
        parsed = urllib.parse.urlsplit(self.path)
        params = urllib.parse.parse_qs(parsed.query)
        try:
            if parsed.path == "/health":
                self.write_json({"ok": True, "mode": "http+proxy+nodriver"})
                return
            if parsed.path == "/resolve":
                input_url = (params.get("url") or [""])[0]
                if not input_url:
                    self.write_json({"ok": False, "error": "Missing url"}, status=400)
                    return
                server_id   = (params.get("server") or [None])[0]
                all_servers = (params.get("all") or ["1"])[0] not in ("0", "false", "False")
                result = resolve(input_url, preferred_server=server_id, all_servers=all_servers)
                self.write_json(result.to_jsonable())
                return
            self.write_json({"ok": False, "error": "Not found"}, status=404)
        except Exception as exc:
            self.write_json({"ok": False, "error": f"{type(exc).__name__}: {exc}"}, status=500)

    def log_message(self, fmt, *args):
        sys.stderr.write("[%s] %s\n" % (self.log_date_time_string(), fmt % args))

    def write_json(self, payload, status=200):
        data = json.dumps(payload, indent=2, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(data)


def serve(host: str, port: int):
    httpd = ThreadingHTTPServer((host, port), ApiHandler)
    print(f"Server: http://{host}:{port}")
    httpd.serve_forever()


def main(argv=None):
    parser = argparse.ArgumentParser(description="Stream resolver (HTTP+proxy+nodriver)")
    parser.add_argument("url", nargs="?", default=DEFAULT_INPUT_URL)
    parser.add_argument("--serve",     action="store_true")
    parser.add_argument("--host",      default="127.0.0.1")
    parser.add_argument("--port",      type=int, default=int(os.environ.get("PORT", "8787")))
    parser.add_argument("--server-id", default=None)
    parser.add_argument("--single",    action="store_true")
    parser.add_argument("--http-only", action="store_true", help="Skip nodriver fallback")
    args = parser.parse_args(argv)

    if args.serve:
        serve(args.host, args.port)
        return 0

    if args.http_only:
        result = resolve_with_http(
            args.url, preferred_server=args.server_id, all_servers=not args.single)
    else:
        result = resolve(
            args.url, preferred_server=args.server_id, all_servers=not args.single)

    print(json.dumps(result.to_jsonable(), indent=2, ensure_ascii=False))
    return 0 if result.ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
