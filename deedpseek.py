#!/usr/bin/env python3
"""
Stream resolver - extracts embed URLs from streamingnow.mov via nodriver.
Intercepts /response.php XHR via CDP to get server list reliably.

Requires:
    pip install nodriver

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

import nodriver as uc
import nodriver.cdp.network as cdp_network

DEFAULT_INPUT_URL = "https://multiembed.mov/?video_id=1339713&tmdb=1"
IS_CI = os.environ.get("CI", "false").lower() == "true"

PAGE_LOAD_WAIT    = 12     # seconds after initial page load
XHR_WAIT          = 10     # seconds to wait for response.php XHR
PLAYVIDEO_WAIT    = 10     # seconds after loading playvideo.php
MAX_SERVER_PAGES  = 10

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


# ── CDP network interception ───────────────────────────────────────────────

async def enable_network_and_intercept(page, captured_responses: dict):
    """
    Enable CDP Network domain and hook ResponseReceived so we can fetch
    the body of /response.php and /playvideo.php XHR calls.
    captured_responses: dict mapping url_fragment → body string (filled in by handler)
    """
    await page.send(cdp_network.enable())

    async def on_response_received(event: cdp_network.ResponseReceived):
        url = event.response.url
        if "response.php" in url or "playvideo.php" in url:
            try:
                body, is_b64 = await page.send(cdp_network.get_response_body(event.request_id))
                for key in ("response.php", "playvideo.php"):
                    if key in url:
                        if key not in captured_responses:
                            captured_responses[key] = []
                        captured_responses[key].append({
                            "url": url,
                            "body": body,
                        })
            except Exception:
                pass

    page.add_handler(cdp_network.ResponseReceived, on_response_received)


# ── Core resolver ──────────────────────────────────────────────────────────

async def resolve_with_nodriver(
    input_url: str,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    result = ResolveResult(input_url=input_url, ok=False, status="nodriver")
    started = time.time()
    sources_to_try = []

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
        browser = await uc.start(
            headless=IS_CI,
            browser_executable_path=chrome_bin,
            user_data_dir=user_data_dir,
        )

        # ── Step 1: open page, enable CDP network interception ─────────────
        captured = {}
        page = await browser.get(input_url)
        await enable_network_and_intercept(page, captured)
        result.steps.append(f"1. CDP network interception enabled")

        await page.sleep(PAGE_LOAD_WAIT)

        current_url = await page.evaluate("window.location.href")
        result.play_url   = current_url
        result.play_token = extract_play_token(current_url)
        result.steps.append(f"2. URL: {current_url[:80]}")
        result.steps.append(f"   token={'yes' if result.play_token else 'no'}")

        # ── Step 2: get sources from intercepted response.php body ─────────
        # Wait a bit more for the XHR to fire
        for _ in range(XHR_WAIT):
            if "response.php" in captured:
                break
            await page.sleep(1)

        response_php_body = None
        if "response.php" in captured:
            response_php_body = captured["response.php"][0]["body"]
            result.steps.append(f"3. Intercepted response.php ({len(response_php_body)} bytes)")
            result.sources = extract_source_choices(response_php_body)
            result.steps.append(f"   Sources from XHR: {len(result.sources)}")
        else:
            result.steps.append(f"3. response.php not intercepted — trying page HTML")

        # Fallback: parse page HTML for sources
        if not result.sources:
            page_html = await page.get_content()
            result.sources = extract_source_choices(page_html)
            result.steps.append(f"   Sources from page HTML: {len(result.sources)}")

        # Fallback: trigger response.php manually via JS fetch
        if not result.sources and result.play_token:
            result.steps.append(f"3b. Fetching response.php via JS...")
            play_origin = urllib.parse.urljoin(current_url, "/")
            response_url = urllib.parse.urljoin(current_url, "/response.php")
            js_result = await page.evaluate(f"""
                (async () => {{
                    try {{
                        const resp = await fetch('{response_url}', {{
                            method: 'POST',
                            headers: {{'Content-Type': 'application/x-www-form-urlencoded', 'X-Requested-With': 'XMLHttpRequest'}},
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

        if not result.play_token:
            result.errors.append("No play token found")
            return result

        if not result.sources:
            result.errors.append("No sources found after all attempts")
            # Dump page HTML snippet for debugging
            page_html = await page.get_content()
            result.steps.append(f"   Page HTML snippet: {page_html[500:1500]}")
            return result

        # ── Step 3: pick servers ────────────────────────────────────────────
        if all_servers:
            sources_to_try = result.sources[:MAX_SERVER_PAGES]
        elif preferred_server:
            sources_to_try = [s for s in result.sources if s.server_id == preferred_server] or result.sources[:1]
        else:
            priority = ["21", "89", "90", "88", "29", "12", "41", "50", "45", "34", "38"]
            ordered  = sorted(result.sources, key=lambda s: priority.index(s.server_id) if s.server_id in priority else 99)
            sources_to_try = ordered[:MAX_SERVER_PAGES]

        result.steps.append(f"4. Processing {len(sources_to_try)} server(s)")

        # ── Step 4: visit each playvideo.php ───────────────────────────────
        for idx, source in enumerate(sources_to_try):
            playvideo_url = (
                urllib.parse.urljoin(result.play_url, "/playvideo.php")
                + f"?video_id={urllib.parse.quote(source.video_id)}"
                + f"&server_id={urllib.parse.quote(source.server_id)}"
                + f"&token={urllib.parse.quote(result.play_token)}&init=1"
            )
            result.steps.append(f"  [{idx+1}] Server {source.server_id}: {source.label[:40]}")

            try:
                # Open in new tab so CDP interception applies fresh
                pv_captured = {}
                pv_page = await browser.get(playvideo_url)
                await enable_network_and_intercept(pv_page, pv_captured)
                await pv_page.sleep(PLAYVIDEO_WAIT)

                pv_html    = await pv_page.get_content()
                pv_cur_url = await pv_page.evaluate("window.location.href")

                found = extract_embed_urls_from_html(pv_html, pv_cur_url)

                # Also check live DOM iframes
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

                # Also check any intercepted playvideo.php XHR bodies
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

    result.embed_urls = unique_keep_order([u for u in result.embed_urls if u and u != "https://"])
    result.ok     = bool(result.embed_urls)
    result.status = "ok" if result.ok else "no_embeds"
    result.stats  = {
        "elapsed_seconds":   round(time.time() - started, 1),
        "sources_found":     len(result.sources),
        "sources_processed": len(sources_to_try),
        "embed_urls_found":  len(result.embed_urls),
        "headless":          IS_CI,
    }
    return result


def resolve(
    input_url: str,
    *,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    return asyncio.run(resolve_with_nodriver(input_url, preferred_server, all_servers))


# ── HTTP API ───────────────────────────────────────────────────────────────

class ApiHandler(BaseHTTPRequestHandler):
    server_version = "StreamResolver/10.0"

    def do_GET(self):
        parsed = urllib.parse.urlsplit(self.path)
        params = urllib.parse.parse_qs(parsed.query)
        try:
            if parsed.path == "/health":
                self.write_json({"ok": True, "mode": "nodriver", "headless": IS_CI})
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
    parser = argparse.ArgumentParser(description="Stream resolver (nodriver + CDP)")
    parser.add_argument("url", nargs="?", default=DEFAULT_INPUT_URL)
    parser.add_argument("--serve",     action="store_true")
    parser.add_argument("--host",      default="127.0.0.1")
    parser.add_argument("--port",      type=int, default=int(os.environ.get("PORT", "8787")))
    parser.add_argument("--server-id", default=None)
    parser.add_argument("--single",    action="store_true")
    args = parser.parse_args(argv)

    if args.serve:
        serve(args.host, args.port)
        return 0

    result = resolve(
        args.url,
        preferred_server=args.server_id,
        all_servers=not args.single,
    )
    print(json.dumps(result.to_jsonable(), indent=2, ensure_ascii=False))
    return 0 if result.ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
