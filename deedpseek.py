#!/usr/bin/env python3
"""
Stream resolver - extracts embed URLs from playvideo.php responses.
With robust rate limiting, exponential backoff, and session management.

Requires:
    pip install curl_cffi

Run:
    python deedpseek.py "https://multiembed.mov/?video_id=1084244&tmdb=1"
"""

from __future__ import annotations

import argparse
import asyncio
import base64
import html
import json
import os
import re
import sys
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import asdict, dataclass, field
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple
import random
import threading
from collections import defaultdict

# Try to import nodriver
try:
    import nodriver as uc
    HAS_NODRIVER = True
except ImportError:
    HAS_NODRIVER = False

# Try to import curl_cffi
try:
    from curl_cffi import requests as curl_requests
    HAS_CURL_CFFI = True
except ImportError:
    HAS_CURL_CFFI = False

DEFAULT_TIMEOUT = 30
STREAMINGNOW_BASE = "https://streamingnow.mov"
DEFAULT_INPUT_URL = "https://multiembed.mov/?video_id=1339713&tmdb=1"
DEFAULT_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/147.0.0.0 Safari/537.36"
)
USE_NODRIVER = False# Set to True to always use nodriver by default

# ─── Rate Limiting Configuration ───────────────────────────────────────────
BASE_DELAY = 3.0          # Base delay between requests (seconds)
MAX_JITTER = 1.5          # Random jitter added to delay
MAX_RETRIES = 3           # Max retries per request
BACKOFF_MULTIPLIER = 2.0  # Exponential backoff multiplier
MAX_BACKOFF = 30.0        # Maximum backoff time (seconds)
MIN_DELAY_BETWEEN_SERVERS = 4.0  # Delay between processing different servers
CONCURRENT_REQUESTS = 1   # Maximum concurrent requests (1 = sequential)
REQUEST_TIMEOUT = 25      # Request timeout

# Per-domain rate limiting
domain_last_request: Dict[str, float] = defaultdict(float)
domain_request_count: Dict[str, int] = defaultdict(int)
MIN_DOMAIN_INTERVAL = 5.0  # Minimum seconds between requests to same domain

# Global lock for thread safety
_rate_lock = threading.Lock()

# Rotating user agents to avoid fingerprinting
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/147.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/146.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/147.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/147.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:136.0) Gecko/20100101 Firefox/136.0",
]

# Regex patterns
PLAY_TOKEN_RE = re.compile(r"""[?&]play=([^&"'<>]+)""", re.IGNORECASE)
LOAD_SOURCES_RE = re.compile(r"""load_sources\((['"])(?P<token>[^'"]+)\1\)""")
IFRAME_SRC_RE = re.compile(r"""<iframe\b[^>]*\bsrc\s*=\s*(['"])(?P<src>.*?)\1""", re.IGNORECASE | re.DOTALL)
SOURCE_LI_RE = re.compile(r"""<li\b(?P<attrs>[^>]*\bdata-id=[^>]*)>""", re.IGNORECASE | re.DOTALL)
ATTR_RE = re.compile(r"""([:\w-]+)\s*=\s*(['"])(.*?)\2""", re.DOTALL)
DATA_SRC_RE = re.compile(r"""data-src\s*=\s*['"]([^'"]+)['"]""", re.IGNORECASE)
SOURCE_FRAME_RE = re.compile(r"""source-frame[^>]*src\s*=\s*['"]([^'"]+)['"]""", re.IGNORECASE)
JS_IFRAME_SRC_RE = re.compile(r"""['"]src['"]\s*:\s*['"]([^'"]+)['"]""", re.IGNORECASE)
JS_SRC_ASSIGN_RE = re.compile(r"""\.src\s*=\s*['"]([^'"]*/(?:e|embed|d)/[^'"]+)['"]""", re.IGNORECASE)
ANY_URL_RE = re.compile(r'https?://[^\s"\'<>]+', re.IGNORECASE)


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


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
    cf_bypass_method: Optional[str] = None

    def to_jsonable(self) -> Dict[str, Any]:
        data = asdict(self)
        data["sources"] = [asdict(item) for item in self.sources]
        return data


def unique_keep_order(items: Iterable[str]) -> List[str]:
    seen = set()
    out = []
    for item in items:
        if item and item not in seen:
            seen.add(item)
            out.append(item)
    return out


def get_random_user_agent() -> str:
    """Return a random user agent to avoid fingerprinting."""
    return random.choice(USER_AGENTS)


def get_domain(url: str) -> str:
    """Extract domain from URL for per-domain rate limiting."""
    try:
        return urllib.parse.urlparse(url).netloc
    except Exception:
        return url


def rate_limit_wait(url: str = ""):
    """
    Smart rate limiting with:
    - Per-domain throttling
    - Random jitter
    - Global request spacing
    """
    with _rate_lock:
        now = time.time()
        wait_time = BASE_DELAY + random.uniform(0, MAX_JITTER)
        
        # Per-domain rate limiting
        if url:
            domain = get_domain(url)
            if domain in domain_last_request:
                elapsed = now - domain_last_request[domain]
                domain_wait = MIN_DOMAIN_INTERVAL - elapsed
                if domain_wait > 0:
                    wait_time = max(wait_time, domain_wait + random.uniform(0, 1))
            
            domain_last_request[domain] = now + wait_time
            domain_request_count[domain] += 1
        
        if wait_time > 0:
            time.sleep(wait_time)


def exponential_backoff(attempt: int, base_delay: float = BASE_DELAY) -> float:
    """Calculate exponential backoff with jitter."""
    delay = min(base_delay * (BACKOFF_MULTIPLIER ** attempt), MAX_BACKOFF)
    jitter = random.uniform(0, delay * 0.5)
    return delay + jitter


def is_valid_embed_url(url: str) -> bool:
    """Check if URL is a valid embed URL (not a junk/ads/menu link)."""
    if not url or not url.startswith("http"):
        return False
    
    skip_patterns = [
        '.js', '.css', '.png', '.jpg', '.svg', '.ico', '.woff', '.gif',
        'googleapis', 'cloudflare', 'gstatic', 'google.com',
        'earn-money', 'api-docs', 'help.', 'example.com',
        '&quot;', '&lt;', '&gt;', '&amp;',
        'cdnjs', 'jsdelivr', 'pagead', 'googlesyndication',
        'facebook.com', 'twitter.com', 'instagram.com',
        'jquery', 'bootstrap', 'fontawesome',
    ]
    
    url_lower = url.lower()
    for pattern in skip_patterns:
        if pattern in url_lower:
            return False
    
    embed_patterns = [
        '/e/', '/embed', '/d/', '/v/',
        'vipstream', 'mixdrop', 'vidmoly',
        'streamwish', 'streamhls', 'dsvplay',
        'voe.sx', 'dood', 'playmogo',
        'streamtape', 'netu', 'filelions',
    ]
    
    for pattern in embed_patterns:
        if pattern in url_lower:
            return True
    
    return False


def request_headers(referer: Optional[str] = None, ajax: bool = False) -> Dict[str, str]:
    """Build request headers with random user agent."""
    headers = {
        "User-Agent": get_random_user_agent(),
        "Accept": "*/*" if ajax else "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Accept-Encoding": "gzip, deflate, br",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
        "DNT": "1",
    }
    if not ajax:
        headers.update({
            "Sec-Ch-Ua": '"Chromium";v="147", "Not?A_Brand";v="99"',
            "Sec-Ch-Ua-Mobile": "?0",
            "Sec-Ch-Ua-Platform": '"Windows"',
            "Sec-Fetch-Dest": "document",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Site": "none",
        })
    else:
        headers.update({
            "X-Requested-With": "XMLHttpRequest",
            "Sec-Fetch-Dest": "empty",
            "Sec-Fetch-Mode": "cors",
            "Sec-Fetch-Site": "same-origin",
        })
    if referer:
        headers["Referer"] = referer
        headers["Origin"] = urllib.parse.urljoin(referer, "/")
    return headers


def http_get_curl_cffi(
    url: str,
    *,
    timeout: int = REQUEST_TIMEOUT,
    referer: Optional[str] = None,
    allow_redirects: bool = True,
    ajax: bool = False,
) -> Optional[Tuple[int, str, Dict[str, str], str]]:
    """Use curl_cffi with rotating browser impersonations."""
    if not HAS_CURL_CFFI or not url or not url.startswith("http"):
        return None
    
    # Rotate impersonations
    impersonations = ["chrome124", "chrome120", "chrome110", "edge101", "safari15_5"]
    random.shuffle(impersonations)
    
    try:
        headers = request_headers(referer, ajax=ajax)
        for impersonate in impersonations[:2]:  # Try 2 random ones
            try:
                session = curl_requests.Session()
                response = session.get(
                    url, headers=headers, impersonate=impersonate,
                    timeout=timeout, allow_redirects=allow_redirects,
                )
                return (response.status_code, str(response.url), dict(response.headers), response.text)
            except Exception:
                continue
    except Exception:
        pass
    return None


def http_get(
    url: str,
    *,
    timeout: int = REQUEST_TIMEOUT,
    referer: Optional[str] = None,
    allow_redirects: bool = True,
    cf_bypass: bool = True,
    ajax: bool = False,
    retry_count: int = 0,
) -> Tuple[int, str, Dict[str, str], str, Optional[str]]:
    """
    HTTP GET with:
    - Rate limiting
    - Exponential backoff retries
    - Per-domain throttling
    """
    if not url or url == "https://" or not url.startswith("http"):
        return 0, url, {}, "", "skipped"
    
    # Apply rate limiting before request
    rate_limit_wait(url)
    
    # Track retries internally
    _retries = retry_count
    
    while True:
        try:
            if cf_bypass and HAS_CURL_CFFI:
                result = http_get_curl_cffi(url, timeout=timeout, referer=referer,
                                           allow_redirects=allow_redirects, ajax=ajax)
                if result:
                    status = result[0]
                    # Handle rate limiting responses
                    if status == 429:
                        if _retries < MAX_RETRIES:
                            delay = exponential_backoff(_retries)
                            _retries += 1
                            time.sleep(delay)
                            continue
                    if status == 403 and _retries < MAX_RETRIES:
                        delay = exponential_backoff(_retries, 5.0)
                        _retries += 1
                        time.sleep(delay)
                        continue
                    return (*result, "curl_cffi")
            
            # Fallback to urllib
            opener = urllib.request.build_opener() if allow_redirects else urllib.request.build_opener(NoRedirect)
            req = urllib.request.Request(url, headers=request_headers(referer, ajax=ajax))
            with opener.open(req, timeout=timeout) as resp:
                body = resp.read().decode("utf-8", errors="replace")
                return resp.status, resp.geturl(), dict(resp.headers.items()), body, "urllib"
                
        except urllib.error.HTTPError as exc:
            if exc.code == 429 and _retries < MAX_RETRIES:
                delay = exponential_backoff(_retries)
                _retries += 1
                time.sleep(delay)
                continue
            if exc.code == 403 and _retries < MAX_RETRIES:
                delay = exponential_backoff(_retries, 5.0)
                _retries += 1
                time.sleep(delay)
                continue
            body = exc.read().decode("utf-8", errors="replace")
            return exc.code, url, dict(exc.headers.items()), body, "urllib"
            
        except Exception as e:
            if _retries < MAX_RETRIES:
                delay = exponential_backoff(_retries)
                _retries += 1
                time.sleep(delay)
                continue
            return 0, url, {}, "", "error"


def http_post_form(
    url: str, form: Dict[str, str],
    *, timeout: int = REQUEST_TIMEOUT, referer: Optional[str] = None, cf_bypass: bool = True,
    retry_count: int = 0,
) -> Tuple[int, str, Dict[str, str], str, Optional[str]]:
    """HTTP POST with rate limiting and retries."""
    rate_limit_wait(url)
    
    _retries = retry_count
    
    while True:
        try:
            if cf_bypass and HAS_CURL_CFFI:
                headers = request_headers(referer, ajax=True)
                for impersonate in ["chrome124", "chrome120"]:
                    try:
                        session = curl_requests.Session()
                        response = session.post(url, data=form, headers=headers, impersonate=impersonate, timeout=timeout)
                        status = response.status_code
                        if status in (429, 403) and _retries < MAX_RETRIES:
                            delay = exponential_backoff(_retries, 5.0 if status == 403 else 2.0)
                            _retries += 1
                            time.sleep(delay)
                            break  # Break inner loop, retry outer
                        return (status, str(response.url), dict(response.headers), response.text, "curl_cffi")
                    except Exception:
                        continue
            
            body = urllib.parse.urlencode(form).encode("utf-8")
            headers = request_headers(referer, ajax=True)
            req = urllib.request.Request(url, data=body, headers=headers, method="POST")
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                text = resp.read().decode("utf-8", errors="replace")
                return resp.status, resp.geturl(), dict(resp.headers.items()), text, "urllib"
                
        except urllib.error.HTTPError as exc:
            if exc.code in (429, 403) and _retries < MAX_RETRIES:
                delay = exponential_backoff(_retries, 5.0 if exc.code == 403 else 2.0)
                _retries += 1
                time.sleep(delay)
                continue
            body = exc.read().decode("utf-8", errors="replace")
            return exc.code, url, dict(exc.headers.items()), body, "urllib"
            
        except Exception:
            if _retries < MAX_RETRIES:
                delay = exponential_backoff(_retries)
                _retries += 1
                time.sleep(delay)
                continue
            return 0, url, {}, "", "error"


def extract_embed_urls_from_playvideo(html_content: str, base_url: str) -> List[str]:
    """
    Extract ONLY the valid embed/iframe URLs from playvideo.php response.
    """
    urls = []
    
    # 1. Standard iframe src
    for match in IFRAME_SRC_RE.finditer(html_content):
        src = html.unescape(match.group("src")).strip()
        full_url = urllib.parse.urljoin(base_url, src) if src else ""
        if src and is_valid_embed_url(full_url):
            urls.append(full_url)
    
    # 2. source-frame src (streamingnow specific)
    for match in SOURCE_FRAME_RE.finditer(html_content):
        src = match.group(1).strip()
        full_url = urllib.parse.urljoin(base_url, src)
        if src and is_valid_embed_url(full_url):
            urls.append(full_url)
    
    # 3. data-src attributes
    for match in DATA_SRC_RE.finditer(html_content):
        src = match.group(1).strip()
        full_url = urllib.parse.urljoin(base_url, src)
        if src and is_valid_embed_url(full_url):
            urls.append(full_url)
    
    # 4. JS iframe src assignment
    for match in JS_IFRAME_SRC_RE.finditer(html_content):
        src = match.group(1).strip()
        if src.startswith('http') and is_valid_embed_url(src):
            urls.append(src)
        elif src.startswith('//') and is_valid_embed_url('https:' + src):
            urls.append('https:' + src)
    
    # 5. JS .src = assignment (embed paths)
    for match in JS_SRC_ASSIGN_RE.finditer(html_content):
        src = match.group(1).strip()
        if src.startswith('http') and is_valid_embed_url(src):
            urls.append(src)
        elif src.startswith('/') and is_valid_embed_url(urllib.parse.urljoin(base_url, src)):
            urls.append(urllib.parse.urljoin(base_url, src))
    
    # 6. Valid embed URLs found anywhere in the page
    all_urls = ANY_URL_RE.findall(html_content)
    for url in all_urls:
        url = url.rstrip('.,;:)!]}\'"')
        if is_valid_embed_url(url) and url not in urls:
            urls.append(url)
    
    return unique_keep_order(urls)


def clean_text(fragment: str) -> str:
    fragment = re.sub(r"<script\b.*?</script>", " ", fragment, flags=re.IGNORECASE | re.DOTALL)
    fragment = re.sub(r"<style\b.*?</style>", " ", fragment, flags=re.IGNORECASE | re.DOTALL)
    fragment = re.sub(r"<[^>]+>", " ", fragment)
    return " ".join(html.unescape(fragment).split())


def extract_source_choices(response_html: str) -> List[SourceChoice]:
    sources = []
    matches = list(SOURCE_LI_RE.finditer(response_html))
    for index, match in enumerate(matches):
        attrs = attrs_to_dict(match.group("attrs"))
        video_id = attrs.get("data-id")
        server_id = attrs.get("data-server")
        if not video_id or not server_id:
            continue
        end = matches[index + 1].start() if index + 1 < len(matches) else response_html.find("</ul>", match.end())
        if end < 0:
            end = min(len(response_html), match.end() + 500)
        fragment = response_html[match.end() : end]
        quality_match = re.search(r"""<span\b[^>]*class=(['"])[^'"]*\bquality\b[^'"]*\1[^>]*>(.*?)</span>""", fragment, re.I | re.S)
        quality = clean_text(quality_match.group(2)) if quality_match else ""
        label = clean_text(fragment)
        sources.append(SourceChoice(video_id=video_id, server_id=server_id, label=label, quality=quality))
    return sources


def attrs_to_dict(raw_attrs: str) -> Dict[str, str]:
    return {name.lower(): html.unescape(value) for name, _, value in ATTR_RE.findall(raw_attrs)}


def extract_play_token(url_or_html: str) -> Optional[str]:
    match = PLAY_TOKEN_RE.search(url_or_html)
    if match:
        return urllib.parse.unquote(match.group(1))
    match = LOAD_SOURCES_RE.search(url_or_html)
    if match:
        return match.group("token")
    return None


def resolve_live_raw(
    input_url: str,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
) -> ResolveResult:
    """Extract embed URLs from playvideo.php with rate limiting."""
    result = ResolveResult(input_url=input_url, ok=False, status="live_raw")
    result.used_live_http = True
    start_time = time.time()
    request_count = 0

    try:
        # Step 1: Initial GET
        status, final_url, headers, body, bypass_method = http_get(
            input_url, allow_redirects=False, cf_bypass=True
        )
        request_count += 1
        result.cf_bypass_method = bypass_method
        result.steps.append(f"1. Initial GET: HTTP {status}")
        
        location = headers.get("Location") or headers.get("location")
        if location:
            result.play_url = urllib.parse.urljoin(input_url, location)
            result.play_token = extract_play_token(result.play_url)
            result.steps.append(f"2. Redirect → streamingnow.mov")
        else:
            result.errors.append("No redirect found")
            return result

        # Step 2: Get play page (with delay)
        time.sleep(MIN_DELAY_BETWEEN_SERVERS)
        status, final_url, headers, page, bypass_method = http_get(
            result.play_url, referer=input_url, cf_bypass=True
        )
        request_count += 1
        result.steps.append(f"3. Play page: HTTP {status}, {len(page)} bytes")
        result.play_token = result.play_token or extract_play_token(page)

        # Step 3: Get sources from response.php (with delay)
        if result.play_token:
            time.sleep(MIN_DELAY_BETWEEN_SERVERS)
            response_url = urllib.parse.urljoin(result.play_url, "/response.php")
            status, _, _, response_html, bypass_method = http_post_form(
                response_url, {"token": result.play_token}, referer=result.play_url, cf_bypass=True
            )
            request_count += 1
            result.steps.append(f"4. response.php: HTTP {status}, {len(response_html)} bytes")
            result.sources = extract_source_choices(response_html)
            result.steps.append(f"5. Found {len(result.sources)} source(s)")
            
            if not result.sources:
                result.errors.append("No sources found")
                return result
            
            # Determine which sources to try
            sources_to_try = []
            if all_servers:
                sources_to_try = result.sources.copy()
            elif preferred_server:
                for s in result.sources:
                    if s.server_id == preferred_server:
                        sources_to_try = [s]
                        break
            if not sources_to_try:
                # Try common server IDs
                priority = ["21", "89", "90", "88", "29", "12", "41", "50", "45", "34", "38"]
                for wanted in priority:
                    for s in result.sources:
                        if s.server_id == wanted and s not in sources_to_try:
                            sources_to_try.append(s)
            if not sources_to_try:
                sources_to_try = result.sources[:5]  # Limit to 5 if all else fails
            
            result.steps.append(f"6. Processing {len(sources_to_try)} server(s)")
            
            # Process each source with delays between them
            for idx, source in enumerate(sources_to_try):
                # Add delay between servers
                if idx > 0:
                    delay = MIN_DELAY_BETWEEN_SERVERS + random.uniform(0, 2)
                    time.sleep(delay)
                
                playvideo_url = urllib.parse.urljoin(
                    result.play_url,
                    f"/playvideo.php?video_id={urllib.parse.quote(source.video_id)}"
                    f"&server_id={urllib.parse.quote(source.server_id)}"
                    f"&token={urllib.parse.quote(result.play_token)}&init=1",
                )
                
                result.steps.append(f"  Server {source.server_id}: {source.label[:50]}")
                
                # Try with retries
                playvideo_html = None
                for attempt in range(MAX_RETRIES):
                    if attempt > 0:
                        backoff = exponential_backoff(attempt - 1, 3.0)
                        time.sleep(backoff)
                    
                    status, _, _, html_text, method = http_get(
                        playvideo_url, referer=result.play_url, cf_bypass=True,
                    )
                    request_count += 1
                    
                    if status == 403:
                        result.steps.append(f"    attempt {attempt+1}: HTTP 403 (CF), waiting {exponential_backoff(attempt, 3.0):.1f}s...")
                        continue
                    
                    if status == 429:
                        result.steps.append(f"    attempt {attempt+1}: HTTP 429 (rate limited), waiting {exponential_backoff(attempt, 5.0):.1f}s...")
                        continue
                    
                    if status == 200 and len(html_text) > 500:
                        playvideo_html = html_text
                        result.steps.append(f"    attempt {attempt+1}: HTTP 200, {len(html_text)} bytes")
                        break
                    elif status == 200:
                        result.steps.append(f"    attempt {attempt+1}: HTTP 200, only {len(html_text)} bytes, retrying...")
                        continue
                    else:
                        result.steps.append(f"    attempt {attempt+1}: HTTP {status}")
                        break
                
                if not playvideo_html:
                    result.steps.append(f"    Failed to get playvideo")
                    continue
                
                # Extract embed URLs
                embed_urls = extract_embed_urls_from_playvideo(playvideo_html, playvideo_url)
                result.steps.append(f"    Found {len(embed_urls)} embed URL(s)")
                
                for eu in embed_urls:
                    if eu not in result.embed_urls:
                        result.embed_urls.append(eu)
                        result.steps.append(f"      → {eu[:80]}")
        
        result.embed_urls = unique_keep_order([u for u in result.embed_urls if u and u != "https://"])
        result.ok = bool(result.embed_urls)
        result.status = "ok" if result.ok else "no_embeds"
        
        # Stats
        elapsed = time.time() - start_time
        result.stats = {
            "total_requests": request_count,
            "elapsed_seconds": round(elapsed, 1),
            "requests_per_second": round(request_count / elapsed, 2) if elapsed > 0 else 0,
            "sources_found": len(result.sources),
            "sources_processed": len(sources_to_try),
            "embed_urls_found": len(result.embed_urls),
        }
        
        if result.ok:
            result.steps.append(f"✓ SUCCESS: {len(result.embed_urls)} embed URL(s) in {elapsed:.1f}s")
        else:
            result.errors.append("No embed URLs extracted.")
        
        return result
        
    except Exception as exc:
        result.status = "error"
        result.errors.append(f"{type(exc).__name__}: {exc}")
        result.stats = {"total_requests": request_count, "elapsed_seconds": round(time.time() - start_time, 1)}
        return result


def resolve(
    input_url: str,
    *,
    live: bool = True,
    preferred_server: Optional[str] = None,
    all_servers: bool = True,
    use_nodriver: bool = False,
) -> ResolveResult:
    if use_nodriver and HAS_NODRIVER:
        result = asyncio.run(resolve_with_nodriver(input_url, preferred_server, all_servers))
        if result.ok:
            return result
        if live:
            http_result = resolve_live_raw(input_url, preferred_server, all_servers)
            result.embed_urls = unique_keep_order(result.embed_urls + http_result.embed_urls)
            result.sources = http_result.sources or result.sources
            result.steps = http_result.steps + result.steps
            result.stats = http_result.stats
            result.ok = bool(result.embed_urls)
            result.status = "ok" if result.ok else result.status
        return result
    
    if live:
        return resolve_live_raw(input_url, preferred_server, all_servers)
    
    return ResolveResult(input_url=input_url, ok=False, status="not_started")


async def resolve_with_nodriver(input_url: str, preferred_server=None, all_servers=True, timeout_ms=60000) -> ResolveResult:
    if not HAS_NODRIVER:
        result = ResolveResult(input_url=input_url, ok=False, status="nodriver_not_installed")
        result.errors.append("nodriver not installed")
        return result
    result = ResolveResult(input_url=input_url, ok=False, status="nodriver")
    result.used_nodriver = True
    result.cf_bypass_method = "nodriver"
    started = time.time()
    try:
        browser = await uc.start(headless=False)
        page = await browser.get(input_url)
        await page.wait_for_timeout(8000)
        page_content = await page.get_content()
        result.play_token = extract_play_token(page_content) or extract_play_token(input_url)
        current_url = await page.evaluate("window.location.href")
        result.embed_urls = extract_embed_urls_from_playvideo(page_content, current_url)
        await browser.stop()
    except Exception as e:
        result.errors.append(f"nodriver: {e}")
        return result
    result.ok = bool(result.embed_urls)
    result.status = "ok" if result.ok else "no_embeds"
    result.stats = {"elapsed_seconds": round(time.time() - started, 1)}
    return result


class ApiHandler(BaseHTTPRequestHandler):
    server_version = "StreamResolver/8.0"

    def do_GET(self):
        parsed = urllib.parse.urlsplit(self.path)
        params = urllib.parse.parse_qs(parsed.query)
        try:
            if parsed.path == "/health":
                self.write_json({"ok": True, "nodriver": HAS_NODRIVER, "curl_cffi": HAS_CURL_CFFI})
                return
            if parsed.path == "/resolve":
                input_url = (params.get("url") or [""])[0]
                if not input_url:
                    self.write_json({"ok": False, "error": "Missing url"}, status=400)
                    return
                server_id = (params.get("server") or [None])[0]
                all_servers = (params.get("all") or ["1"])[0] not in ("0", "false", "False")
                use_nodriver = (params.get("nodriver") or [str(USE_NODRIVER)])[0] not in ("0", "false", "False")
                result = resolve(input_url, preferred_server=server_id, all_servers=all_servers, use_nodriver=use_nodriver)
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


def serve(host, port):
    httpd = ThreadingHTTPServer((host, port), ApiHandler)
    print(f"Server: http://{host}:{port}")
    httpd.serve_forever()


def main(argv=None):
    parser = argparse.ArgumentParser(description="Stream resolver - embed URLs only")
    parser.add_argument("url", nargs="?", default=DEFAULT_INPUT_URL)
    parser.add_argument("--serve", action="store_true")
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=int(os.environ.get("PORT", "8787")))
    parser.add_argument("--server-id", default=None)
    parser.add_argument("--single", action="store_true")
    parser.add_argument("--nodriver", action="store_true")
    args = parser.parse_args(argv)

    if args.serve:
        serve(args.host, args.port)
        return 0

    result = resolve(
        args.url,
        preferred_server=args.server_id,
        all_servers=not args.single,
        use_nodriver=args.nodriver or USE_NODRIVER,
    )
    print(json.dumps(result.to_jsonable(), indent=2, ensure_ascii=False))
    return 0 if result.ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
