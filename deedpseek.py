#!/usr/bin/env python3
"""
Stream resolver - extracts embed URLs from streamingnow.mov.

Strategy:
  1. Pure HTTP path (requests + fake browser headers) — fast, no Chrome needed.
     Works as long as the site doesn't serve a JS challenge to plain HTTP.
  2. Fallback: nodriver (undetected Chrome via CDP) for when CF blocks HTTP.

Requires:
    pip install requests nodriver

Run:
    python deedpseek.py "https://multiembed.mov/?video_id=1084244&tmdb=1"
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


# ── HTTP session builder ───────────────────────────────────────────────────

def make_session() -> requests.Session:
    """Return a requests.Session that looks like a real Chrome browser."""
    s = requests.Session()
    s.headers.update({
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
    })
    s.max_redirects = 10
    return s


# ── Pure-HTTP resolver ─────────────────────────────────────────────────────

def resolve_with_http(
    input_url: str,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    result = ResolveResult(input_url=input_url, ok=False, status="http")
    started = time.time()
    sources_to_try: List[SourceChoice] = []
    total_requests = 0

    sess = make_session()

    try:
        # ── Step 1: GET input URL, follow redirects ────────────────────────
        resp = sess.get(input_url, timeout=30, allow_redirects=False)
        total_requests += 1
        result.steps.append(f"1. Initial GET: HTTP {resp.status_code}")

        if resp.status_code in (301, 302, 303, 307, 308):
            location = resp.headers.get("Location", "")
            result.steps.append(f"2. Redirect → {urllib.parse.urlparse(location).netloc}")
            play_url = location
        elif resp.status_code == 200:
            play_url = resp.url
            result.steps.append(f"2. No redirect, URL: {play_url[:80]}")
        else:
            result.errors.append(f"Unexpected status on initial GET: {resp.status_code}")
            return result

        # Extract token from redirect URL
        result.play_token = extract_play_token(play_url)
        result.play_url   = play_url

        # ── Step 2: GET the play page ──────────────────────────────────────
        # Update Referer to look natural
        sess.headers.update({"Referer": input_url})
        play_resp = sess.get(play_url, timeout=30)
        total_requests += 1
        play_html = play_resp.text
        result.steps.append(f"3. Play page: HTTP {play_resp.status_code}, {len(play_html)} bytes")

        if is_cf_blocked(play_html):
            result.errors.append("Cloudflare challenge on play page — HTTP path blocked")
            result.status = "cf_blocked"
            return result

        # Try extracting token from page HTML if not in URL
        if not result.play_token:
            result.play_token = extract_play_token(play_html)

        if not result.play_token:
            result.errors.append("No play token found in URL or page HTML")
            return result

        # ── Step 3: POST to response.php ───────────────────────────────────
        response_php_url = urllib.parse.urljoin(play_resp.url, "/response.php")
        sess.headers.update({
            "Referer":          play_resp.url,
            "X-Requested-With": "XMLHttpRequest",
            "Content-Type":     "application/x-www-form-urlencoded",
            "Sec-Fetch-Dest":   "empty",
            "Sec-Fetch-Mode":   "cors",
            "Sec-Fetch-Site":   "same-origin",
        })
        rphp = sess.post(
            response_php_url,
            data={"token": result.play_token},
            timeout=30,
        )
        total_requests += 1
        result.steps.append(f"4. response.php: HTTP {rphp.status_code}, {len(rphp.text)} bytes")

        if is_cf_blocked(rphp.text):
            result.errors.append("Cloudflare challenge on response.php — HTTP path blocked")
            result.status = "cf_blocked"
            return result

        result.sources = extract_source_choices(rphp.text)
        result.steps.append(f"5. Found {len(result.sources)} source(s)")

        if not result.sources:
            result.errors.append("No sources found in response.php body")
            return result

        # ── Step 4: pick servers ───────────────────────────────────────────
        if all_servers:
            sources_to_try = result.sources[:MAX_SERVER_PAGES]
        elif preferred_server:
            sources_to_try = [s for s in result.sources if s.server_id == preferred_server] or result.sources[:1]
        else:
            priority = ["21", "89", "90", "88", "29", "12", "41", "50", "45", "34", "38"]
            ordered  = sorted(result.sources, key=lambda s: priority.index(s.server_id) if s.server_id in priority else 99)
            sources_to_try = ordered[:MAX_SERVER_PAGES]

        result.steps.append(f"6. Processing {len(sources_to_try)} server(s)")

        # Reset to document-fetch headers for playvideo.php
        sess.headers.update({
            "Sec-Fetch-Dest": "document",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Site": "same-origin",
            "Content-Type":   "",   # clear POST header
        })
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

                    if is_cf_blocked(pv_html):
                        result.steps.append(f"    CF challenge — skipping")
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

    except Exception as exc:
        result.errors.append(f"HTTP fatal: {type(exc).__name__}: {exc}")
        result.steps.append(f"FATAL: {traceback.format_exc()[-400:]}")

    elapsed = round(time.time() - started, 1)
    result.embed_urls = unique_keep_order([u for u in result.embed_urls if u and u != "https://"])
    result.ok   = bool(result.embed_urls)

    if result.ok:
        result.steps.append(f"✓ SUCCESS: {len(result.embed_urls)} embed URL(s) in {elapsed}s")
        result.status = "ok"
    else:
        result.status = result.status if result.status != "http" else "no_embeds"

    result.stats = {
        "total_requests":     total_requests,
        "elapsed_seconds":    elapsed,
        "requests_per_second": round(total_requests / elapsed, 2) if elapsed else 0,
        "sources_found":      len(result.sources),
        "sources_processed":  len(sources_to_try),
        "embed_urls_found":   len(result.embed_urls),
    }
    result.used_live_http   = True
    result.used_nodriver    = False
    result.cf_bypass_method = "live_http"
    return result


# ── CDP network interception ───────────────────────────────────────────────

async def enable_network_and_intercept(page, captured_responses: dict):
    import nodriver.cdp.network as cdp_network
    await page.send(cdp_network.enable())

    async def on_response_received(event):
        url = event.response.url
        if "response.php" in url or "playvideo.php" in url:
            try:
                body, is_b64 = await page.send(cdp_network.get_response_body(event.request_id))
                for key in ("response.php", "playvideo.php"):
                    if key in url:
                        if key not in captured_responses:
                            captured_responses[key] = []
                        captured_responses[key].append({"url": url, "body": body})
            except Exception:
                pass

    page.add_handler(cdp_network.ResponseReceived, on_response_received)


# ── nodriver fallback resolver ─────────────────────────────────────────────

async def resolve_with_nodriver(
    input_url: str,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    import nodriver as uc
    import nodriver.cdp.network as cdp_network

    result = ResolveResult(input_url=input_url, ok=False, status="nodriver")
    started = time.time()
    sources_to_try: List[SourceChoice] = []

    chrome_bin = (
        shutil.which("google-chrome")
        or shutil.which("google-chrome-stable")
        or shutil.which("chromium-browser")
        or shutil.which("chromium")
        or "/usr/bin/google-chrome"
    )
    user_data_dir = tempfile.mkdtemp(prefix="nodriver_")
    browser = None

    try:
        # Always launch headed — use Xvfb in CI instead of --headless
        extra_args = [
            "--no-sandbox",
            "--disable-dev-shm-usage",
            "--disable-gpu",
            "--window-size=1280,900",
        ]
        browser = await uc.start(
            headless=False,
            browser_executable_path=chrome_bin,
            user_data_dir=user_data_dir,
            browser_args=extra_args,
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
                result.steps.append(f"   JS fetch got {len(str(js_result))} bytes")
                result.sources = extract_source_choices(str(js_result))
                result.steps.append(f"   Sources from JS fetch: {len(result.sources)}")
            else:
                result.steps.append(f"   JS fetch error: {str(js_result)[:100]}")
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
            ordered  = sorted(result.sources, key=lambda s: priority.index(s.server_id) if s.server_id in priority else 99)
            sources_to_try = ordered[:MAX_SERVER_PAGES]

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
        if browser and hasattr(browser, '_process') and browser._process:
            try:
                raw = await asyncio.wait_for(browser._process.stderr.read(4096), timeout=2)
                if raw:
                    result.steps.append(f"Chrome stderr: {raw.decode('utf-8','replace')[-400:]}")
            except Exception:
                pass
    finally:
        if browser:
            try:
                await browser.stop()
            except Exception:
                pass

    elapsed = round(time.time() - started, 1)
    result.embed_urls = unique_keep_order([u for u in result.embed_urls if u and u != "https://"])
    result.ok   = bool(result.embed_urls)
    result.status = "ok" if result.ok else "no_embeds"
    result.stats = {
        "elapsed_seconds":   elapsed,
        "sources_found":     len(result.sources),
        "sources_processed": len(sources_to_try),
        "embed_urls_found":  len(result.embed_urls),
        "headless":          False,
    }
    result.used_live_http   = False
    result.used_nodriver    = True
    result.cf_bypass_method = "nodriver"
    return result


# ── Top-level resolver: HTTP first, nodriver fallback ─────────────────────

def resolve(
    input_url: str,
    *,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    # Try pure-HTTP first — fast and CF-friendly on most IPs
    result = resolve_with_http(input_url, preferred_server=preferred_server, all_servers=all_servers)
    if result.ok:
        return result

    # If CF blocked us or we got nothing, fall back to nodriver
    if result.status in ("cf_blocked", "no_embeds") or not result.sources:
        result.steps.append("→ HTTP failed, falling back to nodriver (Chrome)")
        nd_result = asyncio.run(
            resolve_with_nodriver(input_url, preferred_server=preferred_server, all_servers=all_servers)
        )
        # Merge steps so the full trace is visible
        nd_result.steps = result.steps + nd_result.steps
        return nd_result

    return result


# ── HTTP API ───────────────────────────────────────────────────────────────

class ApiHandler(BaseHTTPRequestHandler):
    server_version = "StreamResolver/11.0"

    def do_GET(self):
        parsed = urllib.parse.urlsplit(self.path)
        params = urllib.parse.parse_qs(parsed.query)
        try:
            if parsed.path == "/health":
                self.write_json({"ok": True, "mode": "http+nodriver"})
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
    parser = argparse.ArgumentParser(description="Stream resolver (HTTP-first + nodriver fallback)")
    parser.add_argument("url", nargs="?", default=DEFAULT_INPUT_URL)
    parser.add_argument("--serve",     action="store_true")
    parser.add_argument("--host",      default="127.0.0.1")
    parser.add_argument("--port",      type=int, default=int(os.environ.get("PORT", "8787")))
    parser.add_argument("--server-id", default=None)
    parser.add_argument("--single",    action="store_true")
    parser.add_argument("--http-only", action="store_true", help="Disable nodriver fallback")
    args = parser.parse_args(argv)

    if args.serve:
        serve(args.host, args.port)
        return 0

    if args.http_only:
        result = resolve_with_http(
            args.url,
            preferred_server=args.server_id,
            all_servers=not args.single,
        )
    else:
        result = resolve(
            args.url,
            preferred_server=args.server_id,
            all_servers=not args.single,
        )

    print(json.dumps(result.to_jsonable(), indent=2, ensure_ascii=False))
    return 0 if result.ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
