#!/usr/bin/env python3
"""
Stream resolver - extracts embed URLs from playvideo.php responses.
Uses nodriver (undetected Chrome) exclusively. Designed for GitHub Actions.

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
import sys
import time
import traceback
import urllib.parse
from dataclasses import asdict, dataclass, field
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

import nodriver as uc

DEFAULT_TIMEOUT = 60
STREAMINGNOW_BASE = "https://streamingnow.mov"
DEFAULT_INPUT_URL = "https://multiembed.mov/?video_id=1339713&tmdb=1"

# ─── nodriver / Chrome configuration ────────────────────────────────────────
# In GitHub Actions: headless=True + extra args for sandboxing
IS_CI = os.environ.get("CI", "false").lower() == "true"

CHROME_ARGS = [
    "--no-sandbox",
    "--disable-setuid-sandbox",
    "--disable-dev-shm-usage",
    "--disable-gpu",
    "--disable-software-rasterizer",
    "--disable-extensions",
    "--disable-background-networking",
    "--disable-sync",
    "--disable-translate",
    "--disable-notifications",
    "--disable-popup-blocking",
    "--window-size=1280,800",
    "--lang=en-US",
    "--mute-audio",
]

PAGE_WAIT_MS       = 10_000   # wait after initial load
SOURCES_WAIT_MS    = 6_000    # wait after clicking a server
PLAYVIDEO_WAIT_MS  = 8_000    # wait for playvideo response
MAX_SERVER_PAGES   = 10       # cap how many servers we process

# Regex patterns
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


# ─── Data classes ─────────────────────────────────────────────────────────────

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


# ─── Helpers ──────────────────────────────────────────────────────────────────

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


# ─── Network-request interceptor helper ──────────────────────────────────────

def _make_request_interceptor(captured: list):
    """
    Returns an async handler that nodriver can attach via page.add_handler.
    Captures XHR/fetch URLs that look like playvideo.php or response.php.
    """
    async def handler(event):
        try:
            url = getattr(event, "request", None)
            if url:
                url = getattr(url, "url", str(url))
            else:
                url = str(event)
            if "playvideo.php" in url or "response.php" in url:
                captured.append(url)
        except Exception:
            pass
    return handler


# ─── Core nodriver resolver ────────────────────────────────────────────────────

async def resolve_with_nodriver(
    input_url: str,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    result = ResolveResult(input_url=input_url, ok=False, status="nodriver")
    started = time.time()

    browser = None
    try:
        browser = await uc.start(
            headless=IS_CI,           # True in CI, False locally (easier to debug)
            browser_args=CHROME_ARGS,
        )

        # ── Step 1: open initial URL (multiembed.mov) ──────────────────────
        page = await browser.get(input_url)
        await page.sleep(PAGE_WAIT_MS / 1000)

        current_url = await page.evaluate("window.location.href")
        result.steps.append(f"1. Loaded: {current_url[:80]}")

        # Grab the play token from the current URL or page source
        page_html = await page.get_content()
        result.play_token = extract_play_token(current_url) or extract_play_token(page_html)
        result.play_url   = current_url

        # ── Step 2: look for source-list items in current page ─────────────
        result.sources = extract_source_choices(page_html)
        result.steps.append(f"2. Sources on initial page: {len(result.sources)}")

        # If no token/sources, maybe we need to wait for a redirect
        if not result.play_token or not result.sources:
            await page.sleep(5)
            current_url = await page.evaluate("window.location.href")
            page_html   = await page.get_content()
            result.play_token = result.play_token or extract_play_token(current_url) or extract_play_token(page_html)
            result.sources    = result.sources or extract_source_choices(page_html)
            result.steps.append(f"   After extra wait: token={'yes' if result.play_token else 'no'}, sources={len(result.sources)}")

        if not result.play_token:
            result.errors.append("Could not find play token")
            return result

        # ── Step 3: pick which servers to process ─────────────────────────
        if all_servers:
            sources_to_try = result.sources[:MAX_SERVER_PAGES]
        elif preferred_server:
            sources_to_try = [s for s in result.sources if s.server_id == preferred_server] or result.sources[:1]
        else:
            priority = ["21", "89", "90", "88", "29", "12", "41", "50", "45", "34", "38"]
            ordered  = sorted(result.sources, key=lambda s: priority.index(s.server_id) if s.server_id in priority else 99)
            sources_to_try = ordered[:MAX_SERVER_PAGES]

        result.steps.append(f"3. Processing {len(sources_to_try)} server(s)")

        # ── Step 4: for each server, navigate playvideo.php directly ───────
        for idx, source in enumerate(sources_to_try):
            playvideo_url = (
                urllib.parse.urljoin(result.play_url, "/playvideo.php")
                + f"?video_id={urllib.parse.quote(source.video_id)}"
                + f"&server_id={urllib.parse.quote(source.server_id)}"
                + f"&token={urllib.parse.quote(result.play_token)}&init=1"
            )

            result.steps.append(f"  [{idx+1}] Server {source.server_id} ({source.label[:40]})")
            result.steps.append(f"      URL: {playvideo_url[:100]}")

            try:
                pv_page = await browser.get(playvideo_url)
                await pv_page.sleep(PLAYVIDEO_WAIT_MS / 1000)

                pv_html    = await pv_page.get_content()
                pv_cur_url = await pv_page.evaluate("window.location.href")

                found = extract_embed_urls_from_html(pv_html, pv_cur_url)
                result.steps.append(f"      → {len(found)} embed URL(s) from page HTML")

                # Also check JS-evaluated iframes
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
                    result.steps.append(f"      + {len(js_urls)} from JS DOM")

                for eu in found:
                    if eu not in result.embed_urls:
                        result.embed_urls.append(eu)
                        result.steps.append(f"      ✓ {eu[:80]}")

            except Exception as exc:
                result.errors.append(f"Server {source.server_id}: {exc}")
                result.steps.append(f"      ✗ error: {exc}")

        # ── Step 5: also scan final page for any leftover embeds ──────────
        try:
            final_html    = await page.get_content()
            final_cur_url = await page.evaluate("window.location.href")
            extra = extract_embed_urls_from_html(final_html, final_cur_url)
            for eu in extra:
                if eu not in result.embed_urls:
                    result.embed_urls.append(eu)
        except Exception:
            pass

    except Exception as exc:
        result.errors.append(f"nodriver fatal: {type(exc).__name__}: {exc}")
        result.steps.append(f"FATAL: {traceback.format_exc()[-300:]}")
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
        "elapsed_seconds": round(time.time() - started, 1),
        "sources_found":    len(result.sources),
        "sources_processed": len(sources_to_try) if result.sources else 0,
        "embed_urls_found":  len(result.embed_urls),
        "headless": IS_CI,
    }
    return result


def resolve(
    input_url: str,
    *,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    return asyncio.run(resolve_with_nodriver(input_url, preferred_server, all_servers))


# ─── HTTP API server ────────────────────────────────────────────────────────

class ApiHandler(BaseHTTPRequestHandler):
    server_version = "StreamResolver/9.0-nodriver"

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
    parser = argparse.ArgumentParser(description="Stream resolver (nodriver only)")
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
