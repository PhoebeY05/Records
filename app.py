from flask import Flask, Response, jsonify, redirect, session, render_template, request, flash, url_for
from flask_session import Session
from cs50 import SQL
from werkzeug.security import check_password_hash, generate_password_hash
from datetime import date, datetime, timedelta
from html import unescape
from html.parser import HTMLParser
import base64
import io
import importlib
import math
import random
import re
import os
import time
import subprocess
import tempfile
import xml.etree.ElementTree as ET
import zipfile
import json
import requests
from bs4 import BeautifulSoup
from urllib.parse import quote_plus, parse_qs, unquote, urlparse
from pathlib import Path
import sys

try:
    from sentence_transformers import SentenceTransformer, util
except Exception:
    SentenceTransformer = None
    util = None

try:
    sync_playwright = importlib.import_module("playwright.sync_api").sync_playwright
except Exception:
    sync_playwright = None


_SEARCH_RESULTS_CACHE = {}
_genre_model = None
app = Flask(__name__)
BOOK_PAGES = {"completed", "unfinished", "tbr"}
BOOK_PAGE_SIZE = 50
DATE_FORMATS = ["%d %B %Y", "%d %b %Y"]


# Configure session to use filesystem (instead of signed cookies)
app.config["SESSION_PERMANENT"] = False
app.config["SESSION_TYPE"] = "filesystem"
Session(app)

# Configure CS50 Library to use SQLite database
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "books.db")
if not os.path.exists(DB_PATH):
    open(DB_PATH, "a").close()
db = SQL(f"sqlite:///{DB_PATH}")


def ensure_schema():
    db.execute(
        """
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT NOT NULL,
            username TEXT NOT NULL,
            hash TEXT NOT NULL,
            date NUMERIC NOT NULL
        )
        """
    )
    db.execute("CREATE UNIQUE INDEX IF NOT EXISTS username ON users (username)")

    db.execute(
        """
        CREATE TABLE IF NOT EXISTS tbr (
            id INTEGER PRIMARY KEY AUTOINCREMENT NOT NULL,
            user_id INTEGER NOT NULL,
            book TEXT NOT NULL,
            status TEXT NOT NULL,
            date NUMERIC NOT NULL,
            notes TEXT,
            genres TEXT,
            series TEXT,
            favorite INTEGER NOT NULL DEFAULT 0,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """
    )

    db.execute(
        """
        CREATE TABLE IF NOT EXISTS unfinished (
            id INTEGER PRIMARY KEY AUTOINCREMENT NOT NULL,
            user_id INTEGER NOT NULL,
            book TEXT NOT NULL,
            date NUMERIC NOT NULL,
            notes TEXT,
            genres TEXT,
            status TEXT NOT NULL DEFAULT 'Finished',
            series TEXT,
            favorite INTEGER NOT NULL DEFAULT 0,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """
    )

    db.execute(
        """
        CREATE TABLE IF NOT EXISTS completed (
            id INTEGER PRIMARY KEY AUTOINCREMENT NOT NULL,
            user_id INTEGER NOT NULL,
            book TEXT NOT NULL,
            date NUMERIC NOT NULL,
            days INTEGER NOT NULL DEFAULT 0,
            notes TEXT,
            reread INTEGER NOT NULL DEFAULT 0,
            genres TEXT,
            status TEXT NOT NULL DEFAULT 'Finished',
            series TEXT,
            favorite INTEGER NOT NULL DEFAULT 0,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """
    )

    db.execute(
        """
        CREATE TABLE IF NOT EXISTS combined (
            id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            book TEXT NOT NULL,
            date NUMERIC NOT NULL,
            page TEXT NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """
    )


ensure_schema()
today = date.today()


def get_page_from_referrer():
    referrer = request.headers.get("Referer", "")
    for page in BOOK_PAGES:
        if page in referrer:
            return page
    return None


def get_status_options(category, user_id):
    rows = db.execute(
        f"SELECT DISTINCT status FROM {category} WHERE user_id = ? AND status IS NOT NULL AND status != '' ORDER BY status",
        user_id,
    )
    return [r["status"] for r in rows]


def get_reread_options(user_id):
    rows = db.execute(
        "SELECT DISTINCT reread FROM completed WHERE user_id = ? ORDER BY reread",
        user_id,
    )
    return [r["reread"] for r in rows]


def _build_books_filter_clause(category, user_id, status_filter=None, existence_filter=None, reread_filter=None):
    query = f"FROM {category} WHERE user_id = ?"
    params = [user_id]
    if status_filter:
        query += " AND status = ?"
        params.append(status_filter)
    if category == "completed" and reread_filter not in (None, ""):
        try:
            reread_value = int(reread_filter)
        except (TypeError, ValueError):
            reread_value = None
        if reread_value is not None:
            query += " AND reread = ?"
            params.append(reread_value)
    if existence_filter in ("genres", "series", "notes"):
        query += f" AND {existence_filter} IS NOT NULL AND {existence_filter} != ''"
        order_clause = f" ORDER BY {existence_filter}"
    else:
        order_clause = " ORDER BY date DESC, id DESC"
    return query, params, order_clause


def query_books_with_filters(category, user_id, status_filter=None, existence_filter=None, reread_filter=None, limit=None, offset=0):
    query, params, order_clause = _build_books_filter_clause(category, user_id, status_filter, existence_filter, reread_filter)
    sql = f"SELECT * {query}{order_clause}"
    if limit is not None:
        sql += " LIMIT ? OFFSET ?"
        params.extend([limit, offset])
    return db.execute(sql, *params)


def count_books_with_filters(category, user_id, status_filter=None, existence_filter=None, reread_filter=None):
    query, params, _ = _build_books_filter_clause(category, user_id, status_filter, existence_filter, reread_filter)
    rows = db.execute(f"SELECT COUNT(*) AS count {query}", *params)
    return rows[0]["count"] if rows else 0


def count_books_missing_genres_with_filters(category, user_id, status_filter=None, existence_filter=None, reread_filter=None):
    query, params, _ = _build_books_filter_clause(category, user_id, status_filter, existence_filter, reread_filter)
    query += " AND (genres IS NULL OR genres = '' OR genres = 'None')"
    rows = db.execute(f"SELECT COUNT(*) AS count {query}", *params)
    return rows[0]["count"] if rows else 0


def sanitize_import_text(text):
    return text.replace("\x00", "")


def _load_genre_model():
    global _genre_model
    if _genre_model is not None:
        return _genre_model
    if SentenceTransformer is None:
        return None
    _genre_model = SentenceTransformer("paraphrase-multilingual-MiniLM-L12-v2")
    return _genre_model


class ImportHTMLParser(HTMLParser):
    BLOCK_TAGS = {"p", "div", "li", "tr", "h1", "h2", "h3", "h4", "h5", "h6"}
    HEADING_FALLBACK_SIZES = {"h1": 72.0, "h2": 60.0, "h3": 48.0, "h4": 36.0, "h5": 24.0, "h6": 18.0}

    def __init__(self):
        super().__init__()
        self.entries = []  # [{"size": float|None, "text": str}]
        self.current_parts = []
        self.current_size = None
        self.in_style = False
        self.style_buffer = []
        self.class_sizes = {}

    def _flush(self):
        text = sanitize_import_text(unescape("".join(self.current_parts))).strip()
        if text:
            self.entries.append({"size": self.current_size, "text": text})
        self.current_parts = []
        self.current_size = None

    @staticmethod
    def _extract_size_from_style(style):
        if not style:
            return None
        match = re.search(r"font-size\s*:\s*([\d.]+)", style)
        if match:
            return float(match.group(1))
        match = re.search(r"font\s*:[^;]*?([\d.]+)\s*(?:px|pt|em)", style)
        if match:
            return float(match.group(1))
        return None

    def _size_from_attrs(self, attrs, tag):
        attrs_dict = dict(attrs)
        for cls in (attrs_dict.get("class") or "").split():
            if cls in self.class_sizes:
                return self.class_sizes[cls]
        size = self._extract_size_from_style(attrs_dict.get("style"))
        if size is not None:
            return size
        if tag in self.HEADING_FALLBACK_SIZES:
            return self.HEADING_FALLBACK_SIZES[tag]
        return None

    def handle_starttag(self, tag, attrs):
        if tag == "style":
            self.in_style = True
            return
        if tag in self.BLOCK_TAGS:
            self._flush()
            self.current_size = self._size_from_attrs(attrs, tag)
        elif tag == "span":
            if self.current_size is None:
                size = self._size_from_attrs(attrs, None)
                if size is not None:
                    self.current_size = size
        elif tag == "br":
            self._flush()

    def handle_endtag(self, tag):
        if tag == "style":
            self.in_style = False
            self._parse_css("".join(self.style_buffer))
            self.style_buffer = []
            return
        if tag in self.BLOCK_TAGS:
            self._flush()

    def _parse_css(self, css):
        for match in re.finditer(r"\.([\w-]+)\s*\{([^}]+)\}", css):
            size = self._extract_size_from_style(match.group(2))
            if size is not None:
                self.class_sizes[match.group(1)] = size

    def handle_data(self, data):
        if self.in_style:
            self.style_buffer.append(data)
        else:
            self.current_parts.append(data)

    def to_lines(self):
        return rank_size_entries(self.entries)


def rank_size_entries(entries):
    """Map each entry's font size to a TBR status prefix based on size ranking."""
    sizes = sorted({e["size"] for e in entries if e["size"] is not None}, reverse=True)
    if len(sizes) < 2:
        # No font-size variation — leave raw text so legacy section markers can be used.
        return [e["text"] for e in entries]

    largest = sizes[0]
    smallest = sizes[-1]
    middles = set(sizes[1:-1])

    output = []
    for entry in entries:
        text = entry["text"]
        size = entry["size"]
        if size == largest:
            output.append(f"[[STATUS:Finished]]{text}")
        elif size in middles:
            output.append(f"[[STATUS:Left Extras]]{text}")
        elif size == smallest:
            output.append(f"[[STATUS:Uncompleted]]{text}")
        else:
            output.append(text)
    return output


def extract_html_text(file_bytes):
    with tempfile.NamedTemporaryFile(suffix=".doc", delete=False) as temp_input:
        temp_input.write(file_bytes)
        temp_path = temp_input.name

    try:
        result = subprocess.run(
            ["textutil", "-convert", "html", "-stdout", temp_path],
            capture_output=True,
            text=True,
            check=True,
        )
        parser = ImportHTMLParser()
        parser.feed(result.stdout)
        parser._flush()
        return "\n".join(parser.to_lines())
    except Exception:
        return None
    finally:
        try:
            os.remove(temp_path)
        except OSError:
            pass


W_NS = "{http://schemas.openxmlformats.org/wordprocessingml/2006/main}"


def _resolve_docx_style_sizes(styles_root):
    """Map style_id -> font size in half-points, following basedOn chains."""
    direct = {}
    based_on = {}
    for style in styles_root.findall(f"{W_NS}style"):
        style_id = style.get(f"{W_NS}styleId")
        if not style_id:
            continue
        sz = style.find(f".//{W_NS}rPr/{W_NS}sz")
        if sz is not None:
            val = sz.get(f"{W_NS}val")
            if val and val.isdigit():
                direct[style_id] = int(val)
        bo = style.find(f"{W_NS}basedOn")
        if bo is not None:
            based_on[style_id] = bo.get(f"{W_NS}val")

    resolved = {}

    def resolve(sid, seen):
        if sid in resolved:
            return resolved[sid]
        if sid in seen:
            return None
        seen.add(sid)
        if sid in direct:
            resolved[sid] = direct[sid]
            return direct[sid]
        parent = based_on.get(sid)
        if parent:
            value = resolve(parent, seen)
            if value is not None:
                resolved[sid] = value
                return value
        return None

    for sid in set(list(direct.keys()) + list(based_on.keys())):
        resolve(sid, set())
    return resolved


def extract_docx_text(file_bytes):
    try:
        with zipfile.ZipFile(io.BytesIO(file_bytes)) as zf:
            try:
                styles_xml = zf.read("word/styles.xml")
            except KeyError:
                styles_xml = None
            try:
                doc_xml = zf.read("word/document.xml")
            except KeyError:
                return None
    except (zipfile.BadZipFile, KeyError):
        return None

    style_sizes = {}
    if styles_xml:
        try:
            style_sizes = _resolve_docx_style_sizes(ET.fromstring(styles_xml))
        except ET.ParseError:
            style_sizes = {}

    try:
        body = ET.fromstring(doc_xml).find(f"{W_NS}body")
    except ET.ParseError:
        return None
    if body is None:
        return None

    default_size = style_sizes.get("Normal") or 24
    entries = []

    for p in body.iter(f"{W_NS}p"):
        style_id = None
        para_size = None
        pPr = p.find(f"{W_NS}pPr")
        if pPr is not None:
            pStyle = pPr.find(f"{W_NS}pStyle")
            if pStyle is not None:
                style_id = pStyle.get(f"{W_NS}val")
            para_sz = pPr.find(f".//{W_NS}rPr/{W_NS}sz")
            if para_sz is not None:
                val = para_sz.get(f"{W_NS}val")
                if val and val.isdigit():
                    para_size = int(val)

        text_parts = []
        max_run_size = None
        for r in p.findall(f"{W_NS}r"):
            run_size = None
            run_sz = r.find(f"{W_NS}rPr/{W_NS}sz")
            if run_sz is not None:
                val = run_sz.get(f"{W_NS}val")
                if val and val.isdigit():
                    run_size = int(val)
            for child in r:
                tag = child.tag
                if tag == f"{W_NS}t" and child.text:
                    text_parts.append(child.text)
                elif tag == f"{W_NS}tab":
                    text_parts.append("\t")
                elif tag == f"{W_NS}br":
                    text_parts.append("\n")
            if run_size is not None:
                max_run_size = run_size if max_run_size is None else max(max_run_size, run_size)

        text = sanitize_import_text("".join(text_parts)).strip()
        if not text:
            continue

        effective = (
            max_run_size
            or para_size
            or (style_sizes.get(style_id) if style_id else None)
            or default_size
        )
        entries.append({"size": float(effective), "text": text})

    if not entries:
        return None
    return "\n".join(rank_size_entries(entries))


def extract_import_text(upload):
    file_name = (upload.filename or "").lower()
    file_bytes = upload.read()

    if file_name.endswith(".docx"):
        docx_text = extract_docx_text(file_bytes)
        if docx_text is not None:
            return docx_text


# --- Genre inference (search first result + page metadata parsing) ---


def _google_search_results(query, max_results=4):
    api_key = os.environ.get("GOOGLE_SEARCH_API_KEY") or os.environ.get("GOOGLE_API_KEY")
    cx = os.environ.get("GOOGLE_SEARCH_CX") or os.environ.get("GOOGLE_CX")
    if api_key and cx:
        try:
            response = requests.get(
                "https://www.googleapis.com/customsearch/v1",
                params={"key": api_key, "cx": cx, "q": query, "num": max_results},
                timeout=8,
            )
            response.raise_for_status()
            data = response.json()
            results = []
            for item in (data.get("items") or [])[:max_results]:
                href = _normalize_search_href(item.get("link") or "")
                results.append(
                    {
                        "title": item.get("title") or "",
                        "snippet": item.get("snippet") or "",
                        "href": href,
                    }
                )
            return _rank_search_results(query, results, max_results=max_results)
        except Exception:
            return []

    return _brave_search_results(query, max_results=max_results)


def _brave_search_results(query, max_results=4):
    cache_key = query.casefold().strip()
    cached = _SEARCH_RESULTS_CACHE.get(cache_key)
    if cached is not None:
        return cached[:max_results]

    try:
        headers = {"User-Agent": "Mozilla/5.0"}
        query_variants = [f"{query} 晋江", query, f"{query} 小说"]
        for search_query in dict.fromkeys(query_variants):
            q = quote_plus(search_query)
            url = f"https://search.brave.com/search?q={q}&source=web"
            response = None
            for attempt in range(3):
                response = requests.get(url, headers=headers, timeout=12)
                if response.status_code != 429:
                    break
                if attempt < 2:
                    time.sleep(1 + attempt)
            if response is None or response.status_code == 429:
                continue
            response.raise_for_status()
            soup = BeautifulSoup(response.text, "html.parser")

            results = []
            seen_urls = set()
            for anchor in soup.select("a[href]"):
                href = anchor.get("href") or ""
                text = anchor.get_text(" ", strip=True)
                if not href or not text:
                    continue
                if href.startswith("javascript:"):
                    continue
                if href.startswith("/search") or href.startswith("/ask") or href.startswith("/images"):
                    continue
                if href.startswith("https://search.brave.com/"):
                    continue
                if href in seen_urls:
                    continue
                seen_urls.add(href)
                results.append({"title": text, "snippet": "", "href": href})
                if len(results) >= max_results:
                    break

            ranked = _rank_search_results(query, results, max_results=max_results)
            if ranked:
                _SEARCH_RESULTS_CACHE[cache_key] = ranked
                return ranked
    except Exception:
        if cached is not None:
            return cached
        return []

    if cached is not None:
        return cached[:max_results]
    return []


def _bing_search_results(query, max_results=4):
    try:
        q = quote_plus(query)
        url = f"https://www.bing.com/search?q={q}"
        headers = {"User-Agent": "Mozilla/5.0"}
        response = requests.get(url, headers=headers, timeout=8)
        response.raise_for_status()
        soup = BeautifulSoup(response.text, "html.parser")
        results = []
        for block in soup.select("li.b_algo"):
            link = block.select_one("h2 a")
            if not link:
                continue
            title = link.get_text(" ", strip=True)
            href = link.get("href") or ""
            snippet_el = block.select_one("p")
            snippet = snippet_el.get_text(" ", strip=True) if snippet_el else ""
            results.append({"title": title, "snippet": snippet, "href": href})
            if len(results) >= max_results:
                break
        return _rank_search_results(query, results, max_results=max_results)
    except Exception:
        return []


def _baidu_search_results(query, max_results=4):
    """Render Baidu via headless Chrome and resolve its /link?url= redirects.

    Why headless: a plain requests call to baidu.com/s returns an anti-bot
    stub page (~1.5 KB) with no result list.
    """
    if sync_playwright is None:
        return []

    cache_key = ("baidu", query.casefold().strip())
    cached = _SEARCH_RESULTS_CACHE.get(cache_key)
    if cached is not None:
        return cached[:max_results]

    chrome_path = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
    raw_items = []
    try:
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch(
                headless=True,
                executable_path=chrome_path if os.path.exists(chrome_path) else None,
            )
            try:
                page = browser.new_page(
                    user_agent=(
                        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                        "AppleWebKit/537.36 (KHTML, like Gecko) "
                        "Chrome/120.0.0.0 Safari/537.36"
                    ),
                    locale="zh-CN",
                )
                page.goto(
                    f"https://www.baidu.com/s?wd={quote_plus(query)}",
                    wait_until="domcontentloaded",
                    timeout=20000,
                )
                try:
                    page.wait_for_selector("#content_left", timeout=8000)
                except Exception:
                    pass
                page.wait_for_timeout(1500)
                raw_items = page.evaluate(
                    """() => {
                        const root = document.querySelector('#content_left') || document.body;
                        const items = Array.from(root.querySelectorAll('div.result, div.c-container'));
                        return items.map(item => {
                            const a = item.querySelector('h3 a') || item.querySelector('a');
                            if (!a) return null;
                            return {
                                title: (a.innerText || '').trim(),
                                href: a.href || '',
                                snippet: (item.innerText || '').trim().slice(0, 240),
                            };
                        }).filter(Boolean);
                    }"""
                )
            finally:
                browser.close()
    except Exception:
        return []

    resolved = []
    seen = set()
    for item in raw_items:
        href = item.get("href") or ""
        if "baidu.com/link?" not in href:
            continue
        real = _resolve_baidu_link(href)
        if not real or real in seen:
            continue
        seen.add(real)
        resolved.append(
            {
                "title": item.get("title") or "",
                "snippet": item.get("snippet") or "",
                "href": real,
            }
        )
        if len(resolved) >= max_results * 2:
            break

    ranked = _rank_search_results(query, resolved, max_results=max_results)
    _SEARCH_RESULTS_CACHE[cache_key] = ranked
    return ranked


def _resolve_baidu_link(href):
    try:
        response = requests.head(
            href,
            allow_redirects=False,
            timeout=6,
            headers={"User-Agent": "Mozilla/5.0"},
        )
        location = response.headers.get("Location")
        if location:
            return location
    except Exception:
        pass
    return href


def _normalize_search_href(href):
    if not href:
        return ""
    parsed = urlparse(href)
    if "google.com" in parsed.netloc and parsed.path == "/url":
        params = parse_qs(parsed.query)
        for key in ("q", "url", "u"):
            values = params.get(key)
            if values and values[0]:
                return unquote(values[0])
    return href


def _result_relevance_score(query, title):
    query_text = sanitize_import_text(query).casefold()
    title_text = sanitize_import_text(title).casefold()
    if not query_text or not title_text:
        return 0.0

    query_tokens = set(re.findall(r"[\w\u4e00-\u9fff]+", query_text))
    title_tokens = set(re.findall(r"[\w\u4e00-\u9fff]+", title_text))
    token_score = 0.0
    if query_tokens:
        token_score = len(query_tokens & title_tokens) / len(query_tokens)

    query_chars = {char for char in query_text if not char.isspace()}
    title_chars = {char for char in title_text if not char.isspace()}
    char_score = 0.0
    if query_chars:
        char_score = len(query_chars & title_chars) / len(query_chars)

    return max(token_score, char_score)


def _rank_search_results(query, results, max_results=4):
    ranked = []
    for index, result in enumerate(results):
        href = result.get("href") or ""
        title = result.get("title") or ""
        if not href:
            continue
        if not href.startswith("http"):
            continue
        parsed = urlparse(href)
        if "google.com" in parsed.netloc:
            continue
        score = _result_relevance_score(query, title)
        if score <= 0:
            continue
        ranked.append((score, index, result))

    ranked.sort(key=lambda item: (-item[0], item[1]))
    return [item[2] for item in ranked[:max_results]]


def _clean_genre_phrase(phrase):
    cleaned = sanitize_import_text(unescape(phrase)).strip()
    cleaned = re.sub(r"^[\s\-–—:;,.\"'()\[\]{}]+|[\s\-–—:;,.\"'()\[\]{}]+$", "", cleaned)
    cleaned = re.sub(r"\s+", " ", cleaned)
    if not cleaned:
        return ""
    if len(cleaned) > 80:
        return ""
    if len(cleaned.split()) > 4:
        return ""
    if not re.search(r"\w", cleaned, flags=re.UNICODE):
        return ""
    return cleaned[:1].upper() + cleaned[1:]


def _normalize_match_text(text):
    return re.sub(r"[\s\W_]+", "", sanitize_import_text(unescape(text)).casefold())


def _extract_ai_genre_candidates(page_text, title, top_k=3):
    model = _load_genre_model()
    if model is None or util is None or not page_text:
        return []

    lines = []
    for raw_line in re.split(r"[\n\r]+", page_text):
        line = sanitize_import_text(unescape(raw_line)).strip()
        if not line:
            continue
        for chunk in re.split(r"[。！？!?；;]+", line):
            chunk = re.sub(r"\s+", " ", chunk).strip()
            if not chunk:
                continue
            lines.append(chunk)

    if not lines:
        return []

    query_text = "book genre tag trope category"
    query_embedding = model.encode(query_text, convert_to_tensor=True)
    line_embeddings = model.encode(lines, convert_to_tensor=True)
    line_scores = util.cos_sim(query_embedding, line_embeddings)[0].cpu().numpy()

    ranked_lines = sorted(
        enumerate(lines),
        key=lambda item: float(line_scores[item[0]]),
        reverse=True,
    )[:6]

    candidate_chunks = []
    chunk_line_scores = {}
    seen = set()
    title_key = _normalize_match_text(title)

    for line_index, line in ranked_lines:
        line_parts = [part.strip() for part in re.split(r"[┃|,，、；;]+", line) if part.strip()]
        if not line_parts:
            line_parts = [line]

        for part in line_parts:
            if re.search(r"[:：]", part):
                prefix, suffix = re.split(r"[:：]", part, maxsplit=1)
                prefix_key = _normalize_match_text(prefix)
                if prefix_key in {"title", "description", "keywords", "genre", "ogtitle", "ogdescription", "bookauthor", "articletag"}:
                    part = suffix.strip()
            cleaned = _clean_genre_phrase(part)
            if not cleaned:
                continue
            chunk_key = _normalize_match_text(cleaned)
            if not chunk_key or chunk_key in seen:
                continue
            if title_key and (title_key in chunk_key or chunk_key in title_key):
                continue
            seen.add(chunk_key)
            candidate_chunks.append(cleaned)
            chunk_line_scores[cleaned] = max(chunk_line_scores.get(cleaned, 0.0), float(line_scores[line_index]))

    if not candidate_chunks:
        return []

    chunk_embeddings = model.encode(candidate_chunks, convert_to_tensor=True)
    chunk_scores = util.cos_sim(query_embedding, chunk_embeddings)[0].cpu().numpy()

    ranked = []
    for idx, chunk in enumerate(candidate_chunks):
        score = float(chunk_scores[idx]) + (chunk_line_scores.get(chunk, 0.0) * 0.35)
        if " " in chunk:
            score += 0.12
        if re.search(r"[:：]", chunk):
            score -= 0.25
        if re.search(r"\d", chunk):
            score -= 0.15
        ranked.append((chunk, score))

    ranked.sort(key=lambda item: (-item[1], item[0]))

    results = []
    results_seen = set()
    for chunk, score in ranked:
        pieces = [piece for piece in re.split(r"[\s,，、/|·]+", chunk) if piece]
        for piece in pieces:
            cleaned = _clean_genre_phrase(piece)
            if not cleaned:
                continue
            piece_key = _normalize_match_text(cleaned)
            if not piece_key or piece_key in results_seen:
                continue
            if title_key and (title_key in piece_key or piece_key in title_key):
                continue
            results_seen.add(piece_key)
            results.append((cleaned, score))
            if len(results) >= top_k:
                return results

    return results[:top_k]


def _extract_structured_genres(text):
    """Extract candidate genres from generic structured label/value rows."""
    if not text:
        return []

    matches = []
    source_text = sanitize_import_text(unescape(text))
    seen = set()
    pending_label = None

    for raw_line in re.split(r"[\n\r]+", source_text):
        line = raw_line.strip()
        if not line or len(line) > 200:
            pending_label = None
            continue
        if "http://" in line.lower() or "https://" in line.lower() or "www." in line.lower():
            pending_label = None
            continue

        if pending_label:
            value = line
            pending_label = None
        else:
            value = ""
            if "：" in line:
                parts = line.split("：", 1)
            elif ":" in line:
                parts = line.split(":", 1)
            else:
                continue

            if len(parts) != 2:
                continue

            label = parts[0].strip()
            value = parts[1].strip()
            if not label:
                continue
            if not value:
                pending_label = label
                continue

        if "：" in line:
            pass

        if not re.search(r"[-－—–/|,]", value):
            continue

        chunks = [c.strip() for c in re.split(r"[-－—–/|,]+", value) if c.strip()]
        if len(chunks) < 2:
            continue
        if any(len(c) > 20 for c in chunks):
            continue
        if any(re.search(r"[《》【】「」『』〈〉]", c) for c in chunks):
            continue
        lengths = [len(c) for c in chunks]
        if max(lengths) / max(1, min(lengths)) > 4:
            continue

        for part in chunks:
            subparts = [part]
            if re.search(r"\s+", part):
                subparts = [piece for piece in re.split(r"\s+", part) if piece]

            for subpart in subparts:
                cleaned = _clean_genre_phrase(subpart)
                if cleaned and not re.search(r"\d", cleaned) and cleaned.casefold() not in seen:
                    seen.add(cleaned.casefold())
                    matches.append(cleaned)
    return matches


def _openlibrary_subjects(title):
    """Query Open Library for subjects (free API)."""
    try:
        q = quote_plus(title)
        url = f"https://openlibrary.org/search.json?q={q}&limit=1"
        r = requests.get(url, timeout=8)
        r.raise_for_status()
        data = r.json()
        docs = data.get("docs") or []
        if not docs:
            return []
        subjects = docs[0].get("subject") or []
        return subjects
    except Exception:
        return []


def _duckduckgo_search_links(query, max_links=3):
    """Use DuckDuckGo HTML search (free) to collect candidate links."""
    try:
        q = quote_plus(query)
        url = f"https://html.duckduckgo.com/html/?q={q}"
        headers = {"User-Agent": "reading-records-bot/1.0"}
        r = requests.get(url, headers=headers, timeout=8)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
        links = []
        for a in soup.select("a.result__a"):
            href = a.get("href")
            if href:
                links.append(href)
            if len(links) >= max_links:
                break
        return links
    except Exception:
        return []


def _fetch_page_text(url, _depth=0):
    try:
        headers = {"User-Agent": "reading-records-bot/1.0"}
        r = requests.get(url, headers=headers, timeout=8)
        r.raise_for_status()
        soup = BeautifulSoup(r.content, "html.parser")
        # Follow <link rel="canonical"> once per call chain. Mobile/AMP/etc.
        # pages frequently advertise the canonical (usually richer) URL here.
        if _depth < 1:
            canonical = soup.find("link", attrs={"rel": "canonical"})
            canonical_href = canonical.get("href") if canonical else None
            if canonical_href and canonical_href.startswith("http") and canonical_href != url:
                return _fetch_page_text(canonical_href, _depth=_depth + 1)
        # Generic metadata and visible text from the page itself.
        texts = []
        for tag in soup.select('script[type="application/ld+json"]'):
            try:
                j = json.loads(tag.string or "{}")
                if isinstance(j, dict):
                    texts.append(json.dumps(j))
            except Exception:
                continue
        for meta_name in ("description", "keywords", "news_keywords"):
            for meta in soup.find_all("meta", attrs={"name": meta_name}):
                content = meta.get("content")
                if content:
                    texts.append(f"{meta_name}: {content}")
        for meta_property in ("og:title", "og:description", "article:tag", "genre", "book:author"):
            for meta in soup.find_all("meta", attrs={"property": meta_property}):
                content = meta.get("content")
                if content:
                    texts.append(f"{meta_property}: {content}")
        desc = soup.find("meta", attrs={"name": "description"})
        if desc and desc.get("content"):
            texts.append(desc.get("content"))
        og = soup.find("meta", property="og:description")
        if og and og.get("content"):
            texts.append(og.get("content"))
        for tag in soup.select("a[rel~=tag], a.tag, li.tag, span.tag, .tag, .tags a, .tags span"):
            tag_text = tag.get_text(" ", strip=True)
            if tag_text:
                texts.append(f"tag: {tag_text}")
        # visible paragraph text (trim)
        body = " ".join(p.get_text(separator=" ", strip=True) for p in soup.find_all("p")[:10])
        if body:
            texts.append(body[:4000])
        text = "\n".join(texts)
        if not _extract_structured_genres(text):
            rendered_text = _fetch_rendered_page_text(url)
            if rendered_text and rendered_text not in text:
                text = f"{text}\n{rendered_text}" if text else rendered_text
        return text
    except Exception:
        rendered_text = _fetch_rendered_page_text(url)
        return rendered_text or ""



def _fetch_rendered_page_text(url):
    if sync_playwright is None:
        return ""

    chrome_path = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
    try:
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch(
                headless=True,
                executable_path=chrome_path if os.path.exists(chrome_path) else None,
            )
            try:
                page = browser.new_page(
                    user_agent=(
                        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                        "AppleWebKit/537.36 (KHTML, like Gecko) "
                        "Chrome/120.0.0.0 Safari/537.36"
                    ),
                )
                response = page.goto(url, wait_until="networkidle", timeout=15000)
                if response is not None and response.status >= 400:
                    return ""
                body_text = page.locator("body").inner_text(timeout=5000)
                return sanitize_import_text(body_text)
            finally:
                browser.close()
    except Exception:
        return ""


DESKTOP_UA = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/120.0.0.0 Safari/537.36"
)


def _genres_from_jjwxc(url):
    """Extract genres from a JJWXC book page (晋江文学城).

    JJWXC novel pages render the category row with one of two labels:
      - desktop: `文章类型：原创-言情-架空历史-奇幻`
      - mobile : `类型：原创-言情-幻想未来-科幻-女主视角`
    """
    text = _fetch_page_text(url)
    if not text:
        return []
    lines = re.split(r"[\n\r]+", text)
    for idx, raw in enumerate(lines):
        line = raw.strip()
        match = re.match(r"^(?:文章)?类型\s*[:：]\s*(.*)$", line)
        if not match:
            continue
        value = match.group(1).strip()
        if not value and idx + 1 < len(lines):
            value = lines[idx + 1].strip()
        if not value:
            continue
        parts = re.split(r"[-－—–/|,]+", value)
        cleaned = [p.strip() for p in parts if p.strip()]
        return [p for p in cleaned if 1 <= len(p) <= 20][:6]
    return []


def _genres_from_goodreads(url):
    """Extract genres from a Goodreads book page.

    Modern Goodreads renders the genre list under `[data-testid="genresList"]`
    with an "...more" sentinel button that we drop.
    """
    if sync_playwright is None:
        return []
    chrome_path = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
    try:
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch(
                headless=True,
                executable_path=chrome_path if os.path.exists(chrome_path) else None,
            )
            try:
                page = browser.new_page(user_agent=DESKTOP_UA, locale="en-US")
                response = page.goto(url, wait_until="domcontentloaded", timeout=20000)
                if response is not None and response.status >= 400:
                    return []
                page.wait_for_timeout(3500)
                genres = page.evaluate(
                    """() => {
                        const collected = [];
                        const selectors = [
                            '[data-testid="genresList"] a',
                            '.BookPageMetadataSection__genres a',
                            'a.bookPageGenreLink',
                        ];
                        for (const sel of selectors) {
                            document.querySelectorAll(sel).forEach(el => {
                                const text = (el.innerText || '').trim();
                                if (text) collected.push(text);
                            });
                            if (collected.length) break;
                        }
                        return collected;
                    }"""
                )
            finally:
                browser.close()
    except Exception:
        return []

    seen = set()
    out = []
    for g in genres:
        if not g or g == "...more":
            continue
        key = g.casefold()
        if key in seen:
            continue
        seen.add(key)
        out.append(g)
    return out[:6]


def _genres_from_qidian(url):
    """Best-effort genre extraction from Qidian (起点).

    Qidian's desktop pages are often protected, but the mobile book page is
    publicly readable and carries the genre/category links we need.
    """
    mobile_url = _normalize_qidian_book_url(url)
    if not mobile_url:
        return []

    try:
        response = requests.get(
            mobile_url,
            headers={"User-Agent": DESKTOP_UA},
            timeout=12,
        )
        response.raise_for_status()
    except Exception:
        return []

    soup = BeautifulSoup(response.text, "html.parser")
    candidates = []
    seen = set()

    def add_candidate(text):
        cleaned = _clean_qidian_genre_candidate(text)
        if not cleaned:
            return
        key = cleaned.casefold()
        if key in seen:
            return
        seen.add(key)
        candidates.append(cleaned)

    for anchor in soup.select('a[href*="/category/"]'):
        add_candidate(anchor.get_text(" ", strip=True))

    lines = [line.strip() for line in soup.get_text("\n", strip=True).splitlines() if line.strip()]
    for line in lines:
        if line in {"简介", "目录", "更多角色", "书友圈", "包含本书的书单"}:
            continue
        if any(token in line for token in ("更新时间", "万字", "书友", "章节", "收藏", "登录", "下载", "App")):
            continue
        if re.search(r"[·|/、,，]", line):
            for part in re.split(r"[·|/、,，]+", line):
                add_candidate(part)

    try:
        intro_index = lines.index("简介")
    except ValueError:
        intro_index = -1
    if intro_index >= 0:
        for line in lines[intro_index + 1 : intro_index + 10]:
            if len(line) > 12:
                break
            add_candidate(line)

    return candidates[:6]


def _normalize_qidian_book_url(url):
    if not url:
        return ""
    parsed = urlparse(url)
    if "qidian.com" not in (parsed.netloc or ""):
        return url
    match = re.search(r"/book/(\d+)/?", parsed.path or "")
    if not match:
        return url
    return f"https://m.qidian.com/book/{match.group(1)}/"


def _clean_qidian_genre_candidate(text):
    cleaned = sanitize_import_text(unescape(text or "")).strip()
    if not cleaned:
        return ""

    cleaned = re.sub(r"\s+", " ", cleaned)
    cleaned = cleaned.strip(" \t\r\n·|/、,，:-：")
    if not cleaned:
        return ""

    if any(
        token in cleaned
        for token in (
            "更新时间",
            "万字",
            "书友",
            "章节",
            "收藏",
            "登录",
            "下载",
            "更多",
            "简介",
            "目录",
            "App",
            "起点中文网",
            "网络小说",
            "小说推荐",
        )
    ):
        return ""

    if "…" in cleaned or "..." in cleaned:
        return ""

    if cleaned.endswith("小说") and len(cleaned) > 2:
        cleaned = cleaned[:-2]

    if len(cleaned) > 20:
        return ""
    if not re.search(r"[\w\u4e00-\u9fff]", cleaned):
        return ""
    return cleaned


def _find_mal_url(title):
    """Use MyAnimeList's prefix-search JSON API to find the top match URL.

    Endpoint: /search/prefix.json?type=manga&keyword=<q>&v=1
    Returns `https://myanimelist.net/manga/<id>/<slug>` for the first item, or
    falls back to the anime search if manga has no hits.
    """
    if not title:
        return None
    base = "https://myanimelist.net/search/prefix.json"
    for kind in ("manga", "anime"):
        try:
            response = requests.get(
                base,
                params={"type": kind, "keyword": title, "v": "1"},
                headers={"User-Agent": DESKTOP_UA},
                timeout=8,
            )
            response.raise_for_status()
            data = response.json()
        except Exception:
            continue
        categories = data.get("categories") or []
        for cat in categories:
            for item in cat.get("items") or []:
                url = item.get("url") or ""
                if url.startswith("http"):
                    return url
    return None


def _genres_from_mal(url):
    """Extract genres from a MAL detail page via `span[itemprop="genre"]`."""
    try:
        response = requests.get(
            url, headers={"User-Agent": DESKTOP_UA}, timeout=10
        )
        response.raise_for_status()
    except Exception:
        return []
    soup = BeautifulSoup(response.text, "html.parser")
    seen = set()
    out = []
    for span in soup.select('span[itemprop="genre"]'):
        text = span.get_text(strip=True)
        if not text:
            continue
        key = text.casefold()
        if key in seen:
            continue
        seen.add(key)
        out.append(text)
    return out[:6]


def _find_goodreads_url(title):
    """Search goodreads.com via Playwright and return the first book-detail URL.

    Goodreads returns a 202 with the anti-bot challenge in flight, but the
    actual results render in the DOM after a few seconds. We wait, then grab
    the first `/book/show/<id>` anchor.
    """
    if sync_playwright is None or not title:
        return None
    chrome_path = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
    search_url = f"https://www.goodreads.com/search?q={quote_plus(title)}"
    try:
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch(
                headless=True,
                executable_path=chrome_path if os.path.exists(chrome_path) else None,
            )
            try:
                page = browser.new_page(user_agent=DESKTOP_UA, locale="en-US")
                page.goto(search_url, wait_until="domcontentloaded", timeout=20000)
                page.wait_for_timeout(8000)
                href = page.evaluate(
                    """() => {
                        const a = document.querySelector('a[href*="/book/show/"]');
                        return a ? a.href : null;
                    }"""
                )
                return href
            finally:
                browser.close()
    except Exception:
        return None


def _google_web_search_results(query, max_results=5):
    """Scrape google.com/search via headless Playwright.

    Bypasses two of Google's basic bot tells:
      - the AutomationControlled blink feature flag (launch arg),
      - the `navigator.webdriver` property (init script).

    These aren't a stealth toolkit; Google can still serve its "unusual
    traffic" CAPTCHA on a hot IP. When that happens we return [] and the
    caller falls back to Bing.
    """
    if sync_playwright is None or not query:
        return []
    chrome_path = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
    search_url = "https://www.google.com/search?q=" + quote_plus(query) + "&hl=en"
    try:
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch(
                headless=True,
                executable_path=chrome_path if os.path.exists(chrome_path) else None,
                args=["--disable-blink-features=AutomationControlled"],
            )
            try:
                context = browser.new_context(
                    user_agent=DESKTOP_UA,
                    locale="en-US",
                    viewport={"width": 1280, "height": 800},
                )
                context.add_init_script(
                    "Object.defineProperty(navigator, 'webdriver', {get: () => undefined})"
                )
                page = context.new_page()
                page.goto(search_url, wait_until="domcontentloaded", timeout=20000)
                page.wait_for_timeout(2500)
                body_head = page.evaluate(
                    "() => document.body ? document.body.innerText.slice(0, 500).toLowerCase() : ''"
                )
                if "unusual traffic" in body_head or "our systems have detected" in body_head:
                    return []
                results = page.evaluate(
                    """(limit) => {
                        const out = [];
                        document.querySelectorAll('a').forEach(a => {
                            const h3 = a.querySelector('h3');
                            if (!h3) return;
                            const href = a.href || '';
                            if (!href.startsWith('http')) return;
                            if (href.includes('google.com/')) return;
                            out.push({
                                title: (h3.innerText || '').trim().slice(0, 200),
                                href: href,
                                snippet: '',
                            });
                        });
                        return out.slice(0, limit);
                    }""",
                    max_results,
                )
                return results
            finally:
                browser.close()
    except Exception:
        return []


def _find_url_on_site(query, domain):
    """Search via Google (Playwright) then Bing, returning the first result
    URL whose host matches `domain` (after decoding Bing's /ck/a wrapper).
    """
    for fetcher in (_google_web_search_results, _bing_search_results):
        try:
            results = fetcher(query, max_results=5) or []
        except Exception:
            results = []
        for result in results:
            href = result.get("href") or ""
            if "bing.com/ck/a" in href:
                href = _decode_bing_redirect(href)
            if href and _matches_domain(href, domain):
                return href
    return None


def _contains_cjk(text):
    return any("一" <= c <= "鿿" for c in (text or ""))


def _decode_bing_redirect(url):
    """Decode Bing's /ck/a?...&u=a1<base64>&... wrapper into the real URL.

    `requests.head(allow_redirects=True)` on these wrappers returns 204 without
    following anywhere — Bing's redirect is server-side and won't fire on HEAD.
    The destination is embedded directly in the `u` parameter as
    "a1" + base64(real_url), so we can decode locally.
    """
    try:
        parsed = urlparse(url)
        if "bing.com" not in parsed.netloc or "/ck/a" not in parsed.path:
            return url
        params = parse_qs(parsed.query)
        encoded = params.get("u", [None])[0]
        if not encoded or not encoded.startswith("a1"):
            return url
        payload = encoded[2:]
        payload += "=" * ((-len(payload)) % 4)
        decoded = base64.urlsafe_b64decode(payload).decode("utf-8", errors="replace")
        if decoded.startswith("http"):
            return decoded
    except Exception:
        pass
    return url


def _matches_domain(url, domain):
    host = (urlparse(url).netloc or "").lower()
    return host == domain or host.endswith("." + domain)


def infer_genres(title, summary=None, top_k=3):
    """Infer genres by looking up the title on the user's trusted sites.

    Routing (set by title language):
      - Chinese (CJK): JJWXC → Qidian
      - English (default): Goodreads → MyAnimeList

    Per-site strategy:
      - Goodreads: native Playwright search; `a[href*="/book/show/"]` → page.
      - MyAnimeList: prefix-search JSON API (no auth, no browser) → page.
      - JJWXC, Qidian: their native search is gated/blocked, so we route
        through the existing search-engine chain (Baidu surfaces those
        domains when not throttled) and filter URLs by hostname.

    Books not on any of these sites return an empty list — by design — so the
    user fills genres manually.
    """
    base_query = title if not summary else f"{title} {summary}"
    title_key = _normalize_match_text(title)

    def _goodreads_step():
        url = _find_goodreads_url(base_query)
        return (url, _genres_from_goodreads(url)) if url else None

    def _mal_step():
        url = _find_mal_url(base_query)
        return (url, _genres_from_mal(url)) if url else None

    def _jjwxc_step():
        url = _find_url_on_site(f"{base_query} 晋江", "jjwxc.net")
        return (url, _genres_from_jjwxc(url)) if url else None

    def _qidian_step():
        url = _find_url_on_site(f"{base_query} 起点", "qidian.com")
        return (url, _genres_from_qidian(url)) if url else None

    if _contains_cjk(base_query):
        steps = (_qidian_step, _jjwxc_step)
    else:
        steps = (_goodreads_step, _mal_step)

    for step in steps:
        outcome = step()
        if not outcome:
            continue
        url, genres = outcome
        if not genres:
            continue

        seen = set()
        ranked = []
        for genre in genres:
            key = genre.casefold()
            if key in seen:
                continue
            genre_key = _normalize_match_text(genre)
            if not genre_key:
                continue
            if title_key and (title_key in genre_key or genre_key in title_key):
                continue
            seen.add(key)
            ranked.append((genre, 1.0, url))
            if len(ranked) >= top_k:
                break
        if ranked:
            return ranked

    return []


@app.route("/api/infer_genres", methods=["POST"])
def api_infer_genres():
    data = request.get_json() or {}
    title = (data.get("title") or "").strip()
    summary = (data.get("summary") or "").strip()
    if not title:
        return {"error": "missing title"}, 400
    out = infer_genres(title, summary)
    return {"title": title, "suggestions": [{"genre": g, "score": s, "source": src} for g, s, src in out]}

    if file_name.endswith((".pages", ".rtf", ".doc", ".docx", ".odt", ".html", ".htm", ".webarchive")):
        rich_text = extract_html_text(file_bytes)
        if rich_text is not None:
            return rich_text

    try:
        return sanitize_import_text(file_bytes.decode("utf-8-sig", errors="ignore"))
    except Exception:
        return None


def session_user_exists():
    if "user_id" not in session:
        return False
    existing = db.execute("SELECT id FROM users WHERE id = ? LIMIT 1", session["user_id"])
    return len(existing) > 0


def normalize_book_key(title):
    return re.sub(r"\s+", " ", title).strip().casefold()


def strip_leading_wrappers(text):
    candidate = sanitize_import_text(text).strip()
    while True:
        unwrapped = re.sub(r"^\s*[\(\[\{（【｛][^\)\]\}）】｝]{1,40}[\)\]\}）】｝]\s*", "", candidate)
        if unwrapped == candidate:
            return candidate
        candidate = unwrapped.strip()


def merge_notes(note_parts):
    merged = []
    seen = set()
    for part in note_parts:
        if not part:
            continue
        cleaned = clean_freeform_note(part)
        if cleaned and cleaned.casefold() not in seen:
            merged.append(cleaned)
            seen.add(cleaned.casefold())
    return "; ".join(merged)


def strip_reread_phrase(text):
    if not text:
        return text
    cleaned = re.sub(
        r"(?i)\bread\s+(?:first|second|third|fourth|\d+(?:st|nd|rd|th)?)\s+times?\b",
        "",
        text,
    )
    cleaned = re.sub(r"\s*;\s*;\s*", "; ", cleaned)
    cleaned = re.sub(r"\s{2,}", " ", cleaned)
    cleaned = re.sub(r"\s*([,;])\s*", r"\1 ", cleaned)
    cleaned = re.sub(r"\s+", " ", cleaned)
    return cleaned.strip(" ;,-")


def should_mark_left_extras(note_parts):
    notes_text = " ".join(part for part in note_parts if part)
    return "番外" in notes_text and "看不到" not in notes_text


def find_existing_book_row(table, user_id, title, columns):
    target_key = normalize_book_key(title)
    rows = db.execute(f"SELECT {columns} FROM {table} WHERE user_id = ?", user_id)
    for row in rows:
        if normalize_book_key(row["book"]) == target_key:
            return row
    return None


def parse_date_text(date_text):
    cleaned = re.sub(r"\s+", " ", date_text).strip().replace(",", "")
    if not cleaned:
        return None

    # ISO date (YYYY-MM-DD) — how dates are stored in the database.
    if re.fullmatch(r"\d{4}-\d{1,2}-\d{1,2}", cleaned):
        try:
            return datetime.strptime(cleaned, "%Y-%m-%d").date()
        except ValueError:
            return None

    # Human form: day full-month-name year (e.g. 21 March 2026)
    if not re.fullmatch(r"\d{1,2}\s+[A-Za-z]+\s+\d{4}", cleaned):
        return None

    for date_format in DATE_FORMATS:
        try:
            return datetime.strptime(cleaned, date_format).date()
        except ValueError:
            continue
    return None


def extract_reread_count(text):
    lowered = text.lower()
    reread = 0
    if "read second time" in lowered:
        reread = max(reread, 1)
    if "read third time" in lowered:
        reread = max(reread, 2)
    if "read fourth time" in lowered:
        reread = max(reread, 3)
    numeric = re.search(r"read\s+(\d+)(?:st|nd|rd|th)?\s+time", lowered)
    if numeric:
        reread = max(reread, max(int(numeric.group(1)) - 1, 0))
    return reread


def parse_common_metadata(text):
    notes = []
    series = None
    favorite = 1 if "✔" in text else 0

    notes.extend([n.strip() for n in re.findall(r"\*(.*?)\*", text) if n.strip()])
    notes.extend([n.strip() for n in re.findall(r"[\{｛](.*?)[\}｝]", text) if n.strip()])

    if re.search(r"#nice\b", text, flags=re.IGNORECASE):
        notes.append("Would recommend to others")

    author_match = re.search(r"作者[:：]\s*([^\]\)）\}]+)", text)
    if author_match:
        notes.append(f"Author disambiguation: {author_match.group(1).strip()}")

    series_match = re.search(r"}\s*(\d+)", text)
    if series_match:
        series = f"Series {series_match.group(1)}"

    return notes, series, favorite


def clean_freeform_note(text):
    cleaned = re.sub(r"\*(.*?)\*", r"\1", text).strip()
    cleaned = re.sub(r"[\{｛](.*?)[\}｝]", r"\1", cleaned)
    cleaned = cleaned.replace("✔️", "").replace("✔", "")
    cleaned = re.sub(r"#nice\b", "", cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r"}\s*\d+", "", cleaned)
    cleaned = re.sub(r"作者[:：]\s*[^\]\)）\}]+", "", cleaned)
    cleaned = strip_reread_phrase(cleaned)
    cleaned = re.sub(r"\s+", " ", cleaned)
    return cleaned.strip("; -*")


def parse_title(raw_title):
    notes = []
    title = strip_leading_wrappers(raw_title)

    title = re.sub(r"\[.*?\]", "", title).strip()

    if "/" in title:
        parts = [p.strip() for p in title.split("/") if p.strip()]
        if parts:
            title = parts[0]
            if len(parts) > 1:
                notes.append(f"AKA: {' / '.join(parts[1:])}")

    return re.sub(r"\s+", " ", title).strip(), notes


def has_book_name_prefix(line):
    stripped = sanitize_import_text(line).strip()
    if not stripped:
        return False

    if stripped.startswith("#") or stripped.startswith("*"):
        return False

    candidate = stripped
    # Remove leading wrappers like (tag), [tag], {tag} repeatedly.
    while True:
        unwrapped = re.sub(r"^\s*[\(\[\{（【｛][^\)\]\}）】｝]{1,40}[\)\]\}）】｝]\s*", "", candidate)
        if unwrapped == candidate:
            break
        candidate = unwrapped.strip()

    # Strip common metadata markers at the very start.
    candidate = re.sub(r"^(?:⭐+|#\w+|✔+|\*+|作者\s*[:：])\s*", "", candidate, flags=re.IGNORECASE)
    if not candidate:
        return False

    return bool(re.search(r"[0-9A-Za-z\u4e00-\u9fff]", candidate))


def parse_completed_line(line):
    if not has_book_name_prefix(line):
        return None

    stripped = line.strip()
    raw_title = stripped
    in_brackets = ""
    tail = ""

    # Prefer the bracket segment that contains a valid date token.
    date_bracket = re.search(r"[（(]\s*(\d{1,2}\s+[A-Za-z]+\s+\d{4})(.*?)[]）)]", stripped)
    if date_bracket:
        raw_title = stripped[: date_bracket.start()].strip()
        in_brackets = stripped[date_bracket.start() + 1 : date_bracket.end() - 1].strip()
        tail = stripped[date_bracket.end() :].strip()

    if not date_bracket:
        bracket_start = None
        for ch in ("（", "("):
            idx = stripped.find(ch)
            if idx != -1 and (bracket_start is None or idx < bracket_start):
                bracket_start = idx

        if bracket_start is not None:
            raw_title = stripped[:bracket_start].strip()
            remainder = stripped[bracket_start + 1 :]
            close_idx = None
            for ch in (")", "）"):
                idx = remainder.find(ch)
                if idx != -1 and (close_idx is None or idx < close_idx):
                    close_idx = idx
            if close_idx is not None:
                in_brackets = remainder[:close_idx].strip()
                tail = remainder[close_idx + 1 :].strip()
            else:
                in_brackets = remainder.strip()

    bracket_text = in_brackets or ""
    date_match = re.search(r"\d{1,2}\s+[A-Za-z]+\s+\d{4}", bracket_text)
    finish_date = parse_date_text(date_match.group(0)) if date_match else None

    bracket_notes = bracket_text
    if date_match:
        bracket_notes = (bracket_text[:date_match.start()] + bracket_text[date_match.end():]).strip()
    bracket_notes = re.sub(r"\bend\b", "", bracket_notes, flags=re.IGNORECASE).strip()

    if finish_date is None:
        # Keep the entry and let importer infer missing date from previous entry.
        pass

    title, title_notes = parse_title(raw_title)
    if not title:
        return None
    common_notes, series, favorite = parse_common_metadata(line)

    notes = []
    notes.extend(title_notes)
    notes.extend(common_notes)
    bracket_without_star = re.sub(r"\*.*?\*", "", bracket_notes)
    tail_without_star = re.sub(r"\*.*?\*", "", tail)
    cleaned_bracket_notes = clean_freeform_note(bracket_without_star)
    cleaned_tail = clean_freeform_note(tail_without_star)
    if cleaned_bracket_notes:
        notes.append(cleaned_bracket_notes)
    if cleaned_tail:
        notes.append(cleaned_tail)

    return {
        "book": title,
        "date": finish_date,
        "notes": notes,
        "series": series,
        "reread": extract_reread_count(line),
        "favorite": favorite,
    }


def parse_tbr_line(line, status=None):
    if not has_book_name_prefix(line):
        return None

    title_section = strip_leading_wrappers(line)
    if status == "Left Extras":
        title_section = re.sub(r"^\s*🙏️?\s*", "", title_section)
    title_section = re.split(r"[（(]", title_section, maxsplit=1)[0]
    title_section = re.split(r"✔|#nice\b|}\s*\d+|\*|\{|｛|⭐", title_section, maxsplit=1, flags=re.IGNORECASE)[0]
    title, title_notes = parse_title(title_section)
    if not title:
        return None

    common_notes, series, favorite = parse_common_metadata(line)
    notes = []
    notes.extend(title_notes)
    notes.extend(common_notes)

    return {
        "book": title,
        "notes": notes,
        "series": series,
        "favorite": favorite,
    }


def parse_tbr_status_marker(line):
    stripped = sanitize_import_text(line).strip()
    if not stripped:
        return None

    prefix_match = re.match(r"^\[\[STATUS:(Finished|Left Extras|Uncompleted)\]\]", stripped, flags=re.IGNORECASE)
    if prefix_match:
        return prefix_match.group(1).title() if prefix_match.group(1).lower() != "left extras" else "Left Extras"

    stripped = re.sub(r"^#{1,6}\s*", "", stripped).strip()
    if re.fullmatch(r"Finished", stripped, flags=re.IGNORECASE):
        return "Finished"
    if re.fullmatch(r"🙏", stripped):
        return "Left Extras"
    if re.fullmatch(r"Left Extras", stripped, flags=re.IGNORECASE):
        return "Left Extras"
    if re.fullmatch(r"Uncompleted", stripped, flags=re.IGNORECASE):
        return "Uncompleted"

    return None


UNFINISHED_STRONG_MARKER_PATTERNS = [
    re.compile(r"第\s*(?:\d+|[一二三四五六七八九十百千零〇两]+)(?:\s+(?:\d+|[一二三四五六七八九十百千零〇两]+))*\s*[章页]", flags=re.IGNORECASE),
    re.compile(r"(?:\d+|[一二三四五六七八九十百千零〇两]+)(?:\s+(?:\d+|[一二三四五六七八九十百千零〇两]+))*\s*[章页]", flags=re.IGNORECASE),
    re.compile(r"(?<!\w)chapter", flags=re.IGNORECASE),
    re.compile(r"(?<!\w)volume", flags=re.IGNORECASE),
    re.compile(r"(?<!\w)pg", flags=re.IGNORECASE),
    re.compile(r"(?<!\w)page", flags=re.IGNORECASE),
]


def extract_unfinished_marker(text):
    matches = [match for pattern in UNFINISHED_STRONG_MARKER_PATTERNS if (match := pattern.search(text))]
    if not matches:
        for token_match in re.finditer(r"\S+", text):
            token = token_match.group(0)
            if token.endswith("章") or token.endswith("页"):
                return token_match.start(), text[token_match.start():]
        return None, text

    match = min(matches, key=lambda item: item.start())
    return match.start(), text[match.start():]


def parse_unfinished_line(line):
    cleaned_line = re.sub(r"\(\s*haven['’]?t read\s*\)", "", line, flags=re.IGNORECASE).strip()

    if not has_book_name_prefix(cleaned_line):
        return None

    marker_start, notes_source = extract_unfinished_marker(cleaned_line)
    status = "Unfinished"
    if marker_start is not None:
        title_source = cleaned_line[:marker_start].strip()
        extra = notes_source.strip()
    else:
        title_source = cleaned_line
        extra = ""

    title, title_notes = parse_title(title_source)
    if not title:
        return None

    common_notes, series, favorite = parse_common_metadata(cleaned_line)
    notes = []
    if extra:
        notes.append(extra)
    notes.extend(title_notes)
    notes.extend(common_notes)

    return {
        "book": title,
        "status": status,
        "notes": notes,
        "series": series,
        "favorite": favorite,
    }


def insert_combined_row(book_id, user_id, book, book_date, page):
    db.execute(
        "INSERT INTO combined (id, user_id, book, date, page) VALUES (?, ?, ?, ?, ?)",
        book_id,
        user_id,
        book,
        book_date,
        page,
    )


def undo_import_actions(user_id, actions):
    for action in reversed(actions):
        action_type = action.get("action")
        table = action.get("table")
        row_id = action.get("id")

        if action_type == "insert":
            db.execute(f"DELETE FROM {table} WHERE id = ? AND user_id = ?", row_id, user_id)
            db.execute(
                "DELETE FROM combined WHERE id = ? AND user_id = ? AND page = ?",
                row_id,
                user_id,
                table,
            )
        elif action_type == "update_completed":
            previous = action.get("previous", {})
            db.execute(
                "UPDATE completed SET reread = ?, notes = ?, favorite = ?, status = ? WHERE id = ? AND user_id = ?",
                previous.get("reread", 0),
                previous.get("notes"),
                previous.get("favorite", 0),
                previous.get("status", "Finished"),
                row_id,
                user_id,
            )
        elif action_type == "update_unfinished":
            previous = action.get("previous", {})
            db.execute(
                "UPDATE unfinished SET status = ?, notes = ?, series = ?, date = ?, favorite = ? WHERE id = ? AND user_id = ?",
                previous.get("status"),
                previous.get("notes"),
                previous.get("series"),
                previous.get("date"),
                previous.get("favorite", 0),
                row_id,
                user_id,
            )
            db.execute(
                "UPDATE combined SET date = ?, book = ? WHERE user_id = ? AND page = 'unfinished' AND id = ?",
                previous.get("combined_date"),
                previous.get("combined_book"),
                user_id,
                row_id,
            )


def import_completed_books(lines, user_id):
    aggregated = {}
    seen_entries = set()
    pending_notes = []
    skipped = 0
    skipped_entries = []
    inserted = 0
    updated = 0
    undo_actions = []

    last_db_date = db.execute("SELECT date FROM completed WHERE user_id = ? ORDER BY date DESC LIMIT 1", user_id)
    last_resolved_date = None
    if last_db_date:
        try:
            last_resolved_date = datetime.strptime(str(last_db_date[0]["date"]), "%Y-%m-%d").date()
        except ValueError:
            last_resolved_date = None

    for raw_line in lines:
        line = sanitize_import_text(raw_line).strip()
        if not line:
            continue
        if line.startswith("⭐"):
            note = line.replace("⭐️", "").replace("⭐", "").strip()
            if note:
                pending_notes.append(note)
            continue

        entry = parse_completed_line(line)
        if entry is None:
            skipped += 1
            skipped_entries.append(raw_line)
            continue

        if entry["date"] is None:
            if last_resolved_date is None:
                entry["date"] = today
            else:
                entry["date"] = last_resolved_date + timedelta(days=1)

        last_resolved_date = entry["date"]

        if pending_notes:
            entry["notes"].extend(pending_notes)
            pending_notes = []

        entry["status"] = "Left Extras" if should_mark_left_extras(entry["notes"]) else "Finished"

        exact_key = (normalize_book_key(entry["book"]), entry["date"].isoformat() if entry["date"] else None)
        if exact_key in seen_entries:
            skipped += 1
            skipped_entries.append(raw_line)
            continue
        seen_entries.add(exact_key)

        key = exact_key[0]
        if key in aggregated:
            existing = aggregated[key]
            if entry["date"] and (existing["date"] is None or entry["date"] < existing["date"]):
                existing["date"] = entry["date"]
            existing["notes"].extend(entry["notes"])
            existing["reread"] += 1
            existing["favorite"] = 1 if (existing.get("favorite") or entry.get("favorite")) else 0
            if entry["status"] == "Left Extras":
                existing["status"] = "Left Extras"
            elif "status" not in existing:
                existing["status"] = "Finished"
            if not existing["series"] and entry["series"]:
                existing["series"] = entry["series"]
        else:
            aggregated[key] = entry

    for entry in aggregated.values():
        existing = find_existing_book_row("completed", user_id, entry["book"], "id, reread, notes, book, favorite, status")
        entry_notes = merge_notes(entry["notes"])

        if existing:
            merged = merge_notes([existing[0]["notes"], entry_notes])
            new_favorite = 1 if (existing[0]["favorite"] or entry.get("favorite")) else 0
            new_status = existing[0]["status"]
            if entry.get("status") == "Left Extras":
                new_status = "Left Extras"
            undo_actions.append(
                {
                    "action": "update_completed",
                    "table": "completed",
                    "id": existing[0]["id"],
                    "previous": {
                        "reread": existing[0]["reread"],
                        "notes": existing[0]["notes"],
                        "favorite": existing[0]["favorite"],
                        "status": existing[0]["status"],
                    },
                }
            )
            db.execute(
                "UPDATE completed SET reread = ?, notes = ?, favorite = ?, status = ? WHERE id = ? AND user_id = ?",
                existing[0]["reread"] + 1,
                merged,
                new_favorite,
                new_status,
                existing[0]["id"],
                user_id,
            )
            updated += 1
            continue

        completed_date = entry["date"] if entry["date"] else date.today()
        latest = db.execute("SELECT date FROM completed WHERE user_id = ? ORDER BY date DESC LIMIT 1", user_id)
        days = 0
        if latest:
            try:
                prev = datetime.strptime(str(latest[0]["date"]), "%Y-%m-%d").date()
                days = max((completed_date - prev).days, 0)
            except ValueError:
                days = 0

        book_id = db.execute(
            "INSERT INTO completed (user_id, book, date, days, notes, reread, status, series, favorite) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            user_id,
            entry["book"],
            completed_date,
            days,
            entry_notes,
            entry["reread"],
            entry.get("status", "Finished"),
            entry["series"],
            entry.get("favorite", 0),
        )
        insert_combined_row(book_id, user_id, entry["book"], completed_date, "completed")
        undo_actions.append({"action": "insert", "table": "completed", "id": book_id})
        inserted += 1

    return inserted, updated, skipped, skipped_entries, undo_actions


def import_tbr_books(lines, user_id):
    aggregated = {}
    pending_notes = []
    current_status = "Uncompleted"
    skipped = 0
    skipped_entries = []
    inserted = 0
    undo_actions = []

    for raw_line in lines:
        line = sanitize_import_text(raw_line).strip()
        if not line:
            continue
        if line.startswith("⭐"):
            note = line.replace("⭐️", "").replace("⭐", "").strip()
            if note:
                pending_notes.append(note)
            continue

        prefixed_status = None
        if line.startswith("[[STATUS:"):
            prefixed_status = parse_tbr_status_marker(line)
            line = re.sub(r"^\[\[STATUS:(?:Finished|Left Extras|Uncompleted)\]\]", "", line, flags=re.IGNORECASE).strip()
            if prefixed_status is not None:
                current_status = prefixed_status

        status_marker = parse_tbr_status_marker(line)
        if status_marker is not None:
            current_status = status_marker
            continue

        entry = parse_tbr_line(line, current_status)
        if entry is None:
            skipped += 1
            skipped_entries.append(raw_line)
            continue

        if pending_notes:
            entry["notes"].extend(pending_notes)
            pending_notes = []

        key = normalize_book_key(entry["book"])
        if key in aggregated:
            existing_entry = aggregated[key]
            existing_entry["favorite"] = 1 if (existing_entry.get("favorite") or entry.get("favorite")) else 0
        else:
            entry["status"] = current_status
            aggregated[key] = entry

    for entry in aggregated.values():
        existing = find_existing_book_row("tbr", user_id, entry["book"], "id, favorite, book")
        if existing:
            if entry.get("favorite") and not existing[0]["favorite"]:
                db.execute(
                    "UPDATE tbr SET favorite = 1 WHERE id = ? AND user_id = ?",
                    existing[0]["id"], user_id,
                )
            continue

        notes_text = merge_notes(entry["notes"])
        book_date = date.today()
        book_id = db.execute(
            "INSERT INTO tbr (user_id, book, status, date, notes, series, favorite) VALUES (?, ?, ?, ?, ?, ?, ?)",
            user_id,
            entry["book"],
            entry.get("status", "Uncompleted"),
            book_date,
            notes_text,
            entry["series"],
            entry.get("favorite", 0),
        )
        insert_combined_row(book_id, user_id, entry["book"], book_date, "tbr")
        undo_actions.append({"action": "insert", "table": "tbr", "id": book_id})
        inserted += 1

    return inserted, 0, skipped, skipped_entries, undo_actions


def import_unfinished_books(lines, user_id):
    aggregated = {}
    pending_notes = []
    skipped = 0
    skipped_entries = []
    inserted = 0
    updated = 0
    undo_actions = []

    for raw_line in lines:
        line = sanitize_import_text(raw_line).strip()
        if not line:
            continue
        if line.startswith("⭐"):
            note = line.replace("⭐️", "").replace("⭐", "").strip()
            if note:
                pending_notes.append(note)
            continue

        entry = parse_unfinished_line(line)
        if entry is None:
            skipped += 1
            skipped_entries.append(raw_line)
            continue

        if pending_notes:
            entry["notes"].extend(pending_notes)
            pending_notes = []

        key = normalize_book_key(entry["book"])
        prior = aggregated.get(key)
        if prior is not None and prior.get("favorite") and not entry.get("favorite"):
            entry["favorite"] = 1
        aggregated[key] = entry

    for entry in aggregated.values():
        existing = find_existing_book_row("unfinished", user_id, entry["book"], "id, notes, status, series, date, book, favorite")
        notes_text = merge_notes(entry["notes"])
        book_date = date.today()

        if existing:
            merged = merge_notes([existing[0]["notes"], notes_text])
            previous_row = db.execute(
                "SELECT status, notes, series, date, book, favorite FROM unfinished WHERE id = ? AND user_id = ? LIMIT 1",
                existing[0]["id"],
                user_id,
            )
            previous_combined = db.execute(
                "SELECT date, book FROM combined WHERE user_id = ? AND page = 'unfinished' AND id = ? LIMIT 1",
                user_id,
                existing[0]["id"],
            )
            new_favorite = 1 if (existing[0]["favorite"] or entry.get("favorite")) else 0
            undo_actions.append(
                {
                    "action": "update_unfinished",
                    "table": "unfinished",
                    "id": existing[0]["id"],
                    "previous": {
                        "status": previous_row[0]["status"] if previous_row else None,
                        "notes": previous_row[0]["notes"] if previous_row else None,
                        "series": previous_row[0]["series"] if previous_row else None,
                        "date": previous_row[0]["date"] if previous_row else None,
                        "favorite": previous_row[0]["favorite"] if previous_row else 0,
                        "combined_date": previous_combined[0]["date"] if previous_combined else None,
                        "combined_book": previous_combined[0]["book"] if previous_combined else None,
                    },
                }
            )
            db.execute(
                "UPDATE unfinished SET status = ?, notes = ?, series = ?, date = ?, favorite = ? WHERE id = ? AND user_id = ?",
                entry["status"],
                merged,
                entry["series"],
                book_date,
                new_favorite,
                existing[0]["id"],
                user_id,
            )
            db.execute(
                "UPDATE combined SET date = ?, book = ? WHERE user_id = ? AND page = 'unfinished' AND id = ?",
                book_date,
                entry["book"],
                user_id,
                existing[0]["id"],
            )
            updated += 1
            continue

        book_id = db.execute(
            "INSERT INTO unfinished (user_id, book, date, notes, status, series, favorite) VALUES (?, ?, ?, ?, ?, ?, ?)",
            user_id,
            entry["book"],
            book_date,
            notes_text,
            entry["status"],
            entry["series"],
            entry.get("favorite", 0),
        )
        insert_combined_row(book_id, user_id, entry["book"], book_date, "unfinished")
        undo_actions.append({"action": "insert", "table": "unfinished", "id": book_id})
        inserted += 1

    return inserted, updated, skipped, skipped_entries, undo_actions

def switch(original, new, book_id):
    original = original.lower()
    new = new.lower()
    latest = db.execute("SELECT * FROM completed WHERE user_id = ? ORDER BY date DESC LIMIT 1", session["user_id"])
    book = db.execute(f"SELECT * FROM {original} WHERE id = ? AND user_id = ?", book_id, session["user_id"])
    db.execute(f"DELETE FROM {original} WHERE id = ? AND user_id = ?", book_id, session["user_id"])
    new_id = db.execute(
        f"INSERT INTO {new} (user_id, book, date, notes, genres, status, series, favorite) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
        session["user_id"],
        book[0]["book"],
        today,
        book[0]["notes"],
        book[0]["genres"],
        book[0]["status"],
        book[0]["series"],
        book[0]["favorite"],
    )
    db.execute("UPDATE combined SET id = ?, page = ? WHERE id = ?", new_id, new, book_id)
    if new == "completed":
        if len(latest) > 0:
            date_format = '%Y-%m-%d'
            prev = datetime.strptime(latest[0]["date"], date_format).date()
            days = (today - prev).days
        else:
            days = 0
        db.execute("UPDATE completed SET days = ? WHERE id = ?", days, new_id)          
    


@app.route("/home", methods = ["GET", "POST"])
def home():
    current_year = date.today().year
    completed_total_count = db.execute("SELECT COUNT(*) AS count FROM completed WHERE user_id = ?", session["user_id"])[0]["count"]
    unfinished_total_count = db.execute("SELECT COUNT(*) AS count FROM unfinished WHERE user_id = ?", session["user_id"])[0]["count"]
    tbr_total_count = db.execute("SELECT COUNT(*) AS count FROM tbr WHERE user_id = ?", session["user_id"])[0]["count"]
    if request.method == "POST":
        if "timeline" in request.form:
            completed_y = request.form.get("completed")
            unfinished_y = request.form.get("unfinished")
            tbr_y = request.form.get("tbr")
            completed = db.execute("SELECT * FROM completed WHERE strftime('%Y', date) = ? AND user_id = ?", completed_y, session["user_id"])
            unfinished = db.execute("SELECT * FROM unfinished WHERE strftime('%Y', date) = ? AND user_id = ?", unfinished_y, session["user_id"])
            tbr = db.execute("SELECT * FROM tbr WHERE strftime('%Y', date) = ? AND user_id = ?", tbr_y, session["user_id"])
            if completed_y == "" or unfinished_y == "" or tbr_y == "":
                flash("Submission failed! Some fields were not filled in.")
                return redirect("/home")
            else:
                return render_template(
                    "home.html",
                    completed=completed,
                    unfinished=unfinished,
                    tbr=tbr,
                    current_year=current_year,
                    completed_total_count=completed_total_count,
                    unfinished_total_count=unfinished_total_count,
                    tbr_total_count=tbr_total_count,
                )
                
        else:
            duration = request.form.get("duration")
            
            if duration == "day":
                day = db.execute("SELECT * FROM combined WHERE date = ? AND user_id = ?", today, session["user_id"])
                return render_template(
                    "home.html",
                    day=day,
                    option="day",
                    current_year=current_year,
                    completed_total_count=completed_total_count,
                    unfinished_total_count=unfinished_total_count,
                    tbr_total_count=tbr_total_count,
                )
            elif duration == "week":
                week = db.execute("SELECT * FROM combined WHERE strftime('%W', date)  = ? AND user_id = ?", today.strftime("%W"), session["user_id"])
                return render_template(
                    "home.html",
                    week=week,
                    option="week",
                    current_year=current_year,
                    completed_total_count=completed_total_count,
                    unfinished_total_count=unfinished_total_count,
                    tbr_total_count=tbr_total_count,
                )
            elif duration == "month":
                month = db.execute("SELECT * FROM combined WHERE strftime('%m', date) = ? AND user_id = ?", '%02d' % today.month, session["user_id"])
                return render_template(
                    "home.html",
                    month=month,
                    option="month",
                    current_year=current_year,
                    completed_total_count=completed_total_count,
                    unfinished_total_count=unfinished_total_count,
                    tbr_total_count=tbr_total_count,
                )
            else:
                flash("Submission failed! No valid options were selected.")
                return redirect("/home")
       
    else:
        return render_template(
            "home.html",
            current_year=current_year,
            completed_total_count=completed_total_count,
            unfinished_total_count=unfinished_total_count,
            tbr_total_count=tbr_total_count,
        )

@app.route("/add", methods=["GET", "POST"])
def add():
    if request.method == "POST":
        name = request.form.get("book")
        category = request.form.get("category")
        status = request.form.get("status")
        genres = request.form.get("genres")
        notes = request.form.get("notes")
        series = request.form.get("series")
        latest = db.execute("SELECT * FROM completed WHERE user_id = ? ORDER BY date DESC LIMIT 1", session["user_id"])
        if name != "" and category in BOOK_PAGES and status != "":
            book_id = db.execute(
                f"INSERT INTO {category} (user_id, book, date, notes, genres, status, series) VALUES (?, ?, ?, ?, ?, ?, ?)",
                session["user_id"],
                name,
                today,
                notes,
                genres,
                status,
                series,
            )
            flash('Add Book Success!')
            db.execute("INSERT INTO combined (id, user_id, book, date, page) VALUES (?,?,?,?,?)", book_id, session["user_id"], name, today, category)
            if category == "completed":
                if latest == []:
                    days = 0
                else:
                    date_format = '%Y-%m-%d'
                    prev = datetime.strptime(latest[0]["date"], date_format).date()
                    days = (today - prev).days
                db.execute("UPDATE completed SET days = ? WHERE id = ?", days, book_id)
            return redirect("/add")
        else:
            flash('Add Book Failed! Some fields were not filled in.')
            return redirect("/add")

    else:
        return render_template("add.html")


@app.route("/import", methods=["GET", "POST"])
def import_books():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")

    if request.method == "GET":
        skipped_entries = session.get("import_skipped_entries", [])
        return render_template("import.html", skipped_entries=skipped_entries)

    category = request.form.get("category")
    upload = request.files.get("books_file")

    if category not in BOOK_PAGES:
        flash("Select a valid category.")
        return redirect("/import")
    if upload is None or upload.filename == "":
        flash("Select a file to import.")
        return redirect("/import")

    content = extract_import_text(upload)
    if content is None:
        flash("Could not read file. Please upload a readable file containing book text.")
        return redirect("/import")

    lines = [sanitize_import_text(line) for line in content.splitlines()]
    if category == "completed":
        inserted, updated, skipped, skipped_entries, undo_actions = import_completed_books(lines, session["user_id"])
    elif category == "tbr":
        inserted, updated, skipped, skipped_entries, undo_actions = import_tbr_books(lines, session["user_id"])
    else:
        inserted, updated, skipped, skipped_entries, undo_actions = import_unfinished_books(lines, session["user_id"])

    session["last_import_undo"] = undo_actions
    session["import_skipped_entries"] = skipped_entries

    flash(f"Import complete for {category}: inserted {inserted}, updated {updated}, skipped {skipped}.")
    return redirect("/import")


@app.route("/import/undo", methods=["POST"])
def undo_import():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")

    undo_actions = session.get("last_import_undo", [])
    if not undo_actions:
        flash("No import is available to undo.")
        return redirect("/import")

    undo_import_actions(session["user_id"], undo_actions)
    session.pop("last_import_undo", None)
    flash("Last import has been undone.")
    return redirect("/import")


@app.route("/import/clear-db", methods=["POST"])
def clear_database():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")

    db.execute("DELETE FROM combined")
    db.execute("DELETE FROM completed")
    db.execute("DELETE FROM unfinished")
    db.execute("DELETE FROM tbr")
    db.execute("DELETE FROM sqlite_sequence WHERE name IN ('combined', 'completed', 'unfinished', 'tbr')")

    session.pop("last_import_undo", None)
    session.pop("import_skipped_entries", None)
    flash("Book data cleared.")
    return redirect("/import")

@app.route("/choose", methods = ["GET", "POST"])
def choose():
    page = get_page_from_referrer()
    if page is None:
        return redirect("/home")
    # Prefer filters sent with this request, otherwise fall back to stored filters
    status_filter = (request.form.get("status_filter") or "").strip() if request.method == "POST" else ""
    existence_filter = (request.form.get("filter") or "").strip() if request.method == "POST" else ""
    reread_filter = (request.form.get("reread_filter") or "").strip() if request.method == "POST" else ""

    if not (status_filter or existence_filter or reread_filter):
        stored = session.get("filters", {}).get(page, {})
        status_filter = stored.get("status_filter", "")
        existence_filter = stored.get("existence_filter", "")
        reread_filter = stored.get("reread_filter", "")

    if status_filter or existence_filter or reread_filter:
        candidates = query_books_with_filters(page, session["user_id"], status_filter, existence_filter, reread_filter)
    else:
        candidates = db.execute(f"SELECT * FROM {page} WHERE user_id = ?", session["user_id"])

    random.shuffle(candidates)
    if not candidates:
        session["selected"] = {"book": "No Books Found", "status":"", "genres": "", "notes":"","series":""}
    else:
        session["selected"] = candidates[0]
    return redirect(f"/{page}")

@app.route("/delete", methods = ["GET", "POST"])
def delete():
    page = get_page_from_referrer()
    id = request.form.get("book")
    if page is None:
        return redirect("/")
    db.execute(f"DELETE FROM {page} WHERE id = ? AND user_id = ?", id, session["user_id"])
    db.execute("DELETE FROM combined WHERE page = ? AND id = ? AND user_id = ?", page, id, session["user_id"])
    return redirect(f"/{page}")

def render_category_page(category, template_name):
    referrer = request.headers.get("Referer") or ""
    if category not in referrer:
        session["selected"] = []
    # Load previously-saved filters for this category
    saved_filters = session.get("filters", {}).get(category, {})
    page_num = 1

    if request.method == "POST":
        # Clear filters when requested
        if "clear" in request.form:
            session.setdefault("filters", {}).pop(category, None)
            status_filter = ""
            existence_filter = ""
            reread_filter = ""
        else:
            # Merge new filters with saved ones so selections stack
            new_status = request.form.get("status_filter")
            new_exist = request.form.get("filter")
            new_reread = request.form.get("reread_filter")

            status_filter = (new_status.strip() if new_status is not None else saved_filters.get("status_filter", ""))
            existence_filter = (new_exist.strip() if new_exist is not None else saved_filters.get("existence_filter", ""))
            reread_filter = (new_reread.strip() if new_reread is not None else saved_filters.get("reread_filter", ""))

            session.setdefault("filters", {})[category] = {
                "status_filter": status_filter,
                "existence_filter": existence_filter,
                "reread_filter": reread_filter,
            }
        page_num = 1
    else:
        status_filter = saved_filters.get("status_filter", "")
        existence_filter = saved_filters.get("existence_filter", "")
        reread_filter = saved_filters.get("reread_filter", "")
        try:
            page_num = max(1, int(request.args.get("page_num", 1)))
        except (TypeError, ValueError):
            page_num = 1

    total_books = count_books_with_filters(category, session["user_id"], status_filter, existence_filter, reread_filter)
    bulk_suggest_count = count_books_missing_genres_with_filters(category, session["user_id"])
    max_page = max(1, math.ceil(total_books / BOOK_PAGE_SIZE)) if total_books else 1
    page_num = min(page_num, max_page)
    offset = (page_num - 1) * BOOK_PAGE_SIZE
    books = query_books_with_filters(
        category,
        session["user_id"],
        status_filter,
        existence_filter,
        reread_filter,
        limit=BOOK_PAGE_SIZE,
        offset=offset,
    )
    has_more = offset + len(books) < total_books
    showing_start = offset + 1 if books else 0
    showing_end = offset + len(books)

    return render_template(
        template_name,
        books=books,
        random=session.get("selected", []),
        selected_status=status_filter,
        selected_existence=existence_filter,
        selected_reread=reread_filter,
        status_options=get_status_options(category, session["user_id"]),
        reread_options=get_reread_options(session["user_id"]) if category == "completed" else [],
        page_num=page_num,
        has_more=has_more,
        total_books=total_books,
        showing_start=showing_start,
        showing_end=showing_end,
        next_page_num=page_num + 1,
        page_size=BOOK_PAGE_SIZE,
        bulk_suggest_count=bulk_suggest_count,
    )


@app.route("/favorites")
def favorites():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")

    section_specs = [
        ("completed", "Completed"),
        ("tbr", "To Be Read"),
        ("unfinished", "Unfinished"),
    ]
    sections = []
    total = 0
    for category, label in section_specs:
        books = db.execute(
            f"SELECT * FROM {category} WHERE user_id = ? AND favorite = 1 ORDER BY date DESC, id DESC",
            session["user_id"],
        )
        total += len(books)
        sections.append({"category": category, "label": label, "books": books})

    return render_template("favorites.html", sections=sections, total=total)


@app.route("/tbr", methods=["GET", "POST"])
def tbr():
    if request.method == "POST":
        if "change" in request.form:
            change = request.form.get("change")
            book_id = request.form.get("book")
            temp = re.findall(r'\d+', book_id)
            book_id = list(map(int, temp))[0]
            if change == "tick":
                switch("tbr", "completed", book_id)
            elif change == "cross":
                switch("tbr", "unfinished", book_id)
            return redirect("/tbr")
        if "clear" in request.form:
            session.setdefault("filters", {}).pop("tbr", None)
            return redirect("/tbr")
    return render_category_page("tbr", "tbr.html")


@app.route("/completed", methods=["GET", "POST"])
def completed():
    if request.method == "POST":
        if "book" in request.form:
            id = request.form.get("book")
            times = db.execute("SELECT * FROM completed WHERE id = ? AND user_id = ?", id, session["user_id"])[0]["reread"]
            db.execute("UPDATE completed SET reread = ? WHERE id = ? AND user_id = ?", times + 1, id, session["user_id"])
            return redirect("/completed")
        if "clear" in request.form:
            session.setdefault("filters", {}).pop("completed", None)
            return redirect("/completed")
    return render_category_page("completed", "completed.html")


@app.route("/unfinished", methods=["GET", "POST"])
def unfinished():
    if request.method == "POST":
        if "change" in request.form:
            change = request.form.get("change")
            book_id = request.form.get("book")
            temp = re.findall(r'\d+', book_id)
            id = list(map(int, temp))[0]
            if change == "tick":
                switch("unfinished", "completed", id)
            elif change == "cross":
                switch("unfinished", "tbr", id)
            return redirect("/unfinished")
        if "clear" in request.form:
            session.setdefault("filters", {}).pop("unfinished", None)
            return redirect("/unfinished")
    return render_category_page("unfinished", "unfinished.html")


@app.route("/api/book/<category>/<int:book_id>")
def book_detail_api(category, book_id):
    if not session_user_exists():
        return {"error": "unauthorized"}, 401
    if category not in BOOK_PAGES:
        return {"error": "invalid category"}, 404
    rows = db.execute(
        f"SELECT * FROM {category} WHERE id = ? AND user_id = ? LIMIT 1",
        book_id, session["user_id"],
    )
    if not rows:
        return {"error": "not found"}, 404
    book = rows[0]
    payload = {
        "id": book["id"],
        "category": category,
        "book": book["book"],
        "status": book.get("status") or "",
        "date": str(book.get("date") or ""),
        "genres": book.get("genres") or "",
        "notes": book.get("notes") or "",
        "series": book.get("series") or "",
    }
    if "reread" in book:
        payload["reread"] = book["reread"]
    if "days" in book:
        payload["days"] = book["days"]
    return payload


def serialize_book_row(category, book):
    payload = {
        "id": book["id"],
        "category": category,
        "book": book["book"],
        "status": book.get("status") or "",
        "date": str(book.get("date") or ""),
        "genres": book.get("genres") or "",
        "notes": book.get("notes") or "",
        "series": book.get("series") or "",
    }
    if "reread" in book:
        payload["reread"] = book["reread"]
    if "days" in book:
        payload["days"] = book["days"]
    return payload


@app.route("/favorite/<category>/<int:book_id>", methods=["POST"])
def toggle_favorite(category, book_id):
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")
    if category not in BOOK_PAGES:
        return redirect("/home")

    rows = db.execute(
        f"SELECT favorite FROM {category} WHERE id = ? AND user_id = ? LIMIT 1",
        book_id, session["user_id"],
    )
    if not rows:
        flash("That book no longer exists.")
        return redirect(f"/{category}")

    new_value = 0 if rows[0]["favorite"] else 1
    db.execute(
        f"UPDATE {category} SET favorite = ? WHERE id = ? AND user_id = ?",
        new_value, book_id, session["user_id"],
    )
    redirect_to = (request.form.get("redirect_to") or "").strip()
    if not redirect_to:
        redirect_to = f"/{category}#book-{book_id}"
    return redirect(redirect_to)


@app.route("/update/<category>/<int:book_id>", methods=["POST"])
def update_book(category, book_id):
    if not session_user_exists():
        session.clear()
        if request.headers.get("X-Requested-With") == "XMLHttpRequest":
            return jsonify({"error": "Your session is no longer valid. Please log in again."}), 401
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")

    if category not in BOOK_PAGES:
        if request.headers.get("X-Requested-With") == "XMLHttpRequest":
            return jsonify({"error": "Invalid category."}), 400
        flash("Invalid category.")
        return redirect("/home")

    expects_json = request.headers.get("X-Requested-With") == "XMLHttpRequest"
    book_name = (request.form.get("book") or "").strip()
    status = (request.form.get("status") or "").strip()
    genres = (request.form.get("genres") or "").strip()
    series = (request.form.get("series") or "").strip()
    notes = (request.form.get("notes") or "").strip()
    reread_raw = (request.form.get("reread") or "").strip()
    reread = None
    if category == "completed" and reread_raw != "":
        try:
            reread = max(int(reread_raw), 0)
        except ValueError:
            if expects_json:
                return jsonify({"error": "Rereads must be a whole number."}), 400
            flash("Rereads must be a whole number.")
            return redirect(f"/{category}")
    elif category == "completed" and reread_raw == "":
        if expects_json:
            return jsonify({"error": "Rereads cannot be blank."}), 400
        flash("Rereads cannot be blank.")
        return redirect(f"/{category}")

    if not book_name:
        if expects_json:
            return jsonify({"error": "Book name cannot be empty."}), 400
        flash("Book name cannot be empty.")
        return redirect(f"/{category}")

    existing = db.execute(
        f"SELECT id FROM {category} WHERE id = ? AND user_id = ? LIMIT 1",
        book_id, session["user_id"],
    )
    if not existing:
        if expects_json:
            return jsonify({"error": "That book no longer exists."}), 404
        flash("That book no longer exists.")
        return redirect(f"/{category}")

    if category == "completed" and reread is not None:
        db.execute(
            f"UPDATE {category} SET book = ?, status = ?, genres = ?, series = ?, notes = ?, reread = ? "
            "WHERE id = ? AND user_id = ?",
            book_name, status, genres, series, notes, reread,
            book_id, session["user_id"],
        )
    else:
        db.execute(
            f"UPDATE {category} SET book = ?, status = ?, genres = ?, series = ?, notes = ? "
            "WHERE id = ? AND user_id = ?",
            book_name, status, genres, series, notes,
            book_id, session["user_id"],
        )
    db.execute(
        "UPDATE combined SET book = ? WHERE id = ? AND user_id = ? AND page = ?",
        book_name, book_id, session["user_id"], category,
    )

    updated = db.execute(
        f"SELECT * FROM {category} WHERE id = ? AND user_id = ? LIMIT 1",
        book_id, session["user_id"],
    )[0]

    if expects_json:
        return jsonify(serialize_book_row(category, updated))

    flash("Book updated.")
    return redirect(f"/{category}")


def _parse_genre_list(text):
    if not text:
        return []
    cleaned = sanitize_import_text(text)
    parts = re.split(r"[,，、;；/|]+", cleaned)
    return [p.strip() for p in parts if p.strip()]


def _genre_freq(rows):
    freq = {}
    for row in rows:
        for genre in row["genres_list"]:
            freq[genre] = freq.get(genre, 0) + 1
    return freq


def _cosine_distance(a, b):
    if not a or not b:
        return 1.0 if (a or b) else 0.0
    keys = set(a) | set(b)
    dot = sum(a.get(k, 0) * b.get(k, 0) for k in keys)
    na = math.sqrt(sum(v * v for v in a.values())) or 1.0
    nb = math.sqrt(sum(v * v for v in b.values())) or 1.0
    return 1.0 - dot / (na * nb)


def _find_time_breaks(rows, min_gap_days=45, median_factor=5.0):
    """Find indices where consecutive completions are separated by a real break.

    A "break" is a gap that is both absolutely large (≥ `min_gap_days`) and
    relatively large (≥ `median_factor` × median gap between reads for this
    user). Tuning the two together avoids treating a heavy reader's normal pace
    as a break, while still catching the case where someone reads a book per
    week for years and then disappears for six months.

    Returns a sorted list of indices `i` such that there is a break between
    rows[i-1] and rows[i].
    """
    if len(rows) < 2:
        return []
    gaps = [
        (rows[i]["date"] - rows[i - 1]["date"]).days
        for i in range(1, len(rows))
    ]
    nonzero = [g for g in gaps if g > 0]
    if not nonzero:
        return []
    sorted_gaps = sorted(nonzero)
    median = sorted_gaps[len(sorted_gaps) // 2]
    threshold = max(min_gap_days, median * median_factor)
    return [i for i, g in enumerate(gaps, start=1) if g >= threshold]


def _find_change_points(rows, min_period=5, max_periods=12, min_gain=0.15):
    """Segment a reading history into periods using two signals.

    1. Time breaks — gaps in reading where the user stopped for an unusually
       long time. These are the strongest, most natural boundaries.
    2. Content shifts — binary segmentation on the genre-frequency signal,
       to split a single long stretch of reading into sub-periods if the
       genre mix changes meaningfully.

    `min_period` only constrains *content-based* splits — it stops the genre
    detector from producing tiny (2–3 book) periods that are mostly noise.
    Time-break splits are unconditional, since a real multi-month gap is
    meaningful even if only a few books surround it.

    Returns a sorted list of split indices including 0 and len(rows), so
    consecutive pairs define each period.
    """
    n = len(rows)
    if n == 0:
        return [0, 0]

    # Step 1: every break in the history becomes a hard boundary.
    splits = {0, n}
    for b in _find_time_breaks(rows):
        splits.add(b)

    # Step 2: greedily subdivide remaining long segments by genre shift, but
    # only as long as the cosine gap clears the (now looser) threshold.
    while len(splits) - 1 < max_periods:
        splits_sorted = sorted(splits)
        best_split = None
        best_gain = 0.0
        for i in range(len(splits_sorted) - 1):
            start, end = splits_sorted[i], splits_sorted[i + 1]
            if end - start < 2 * min_period:
                continue
            for candidate in range(start + min_period, end - min_period + 1):
                left = _genre_freq(rows[start:candidate])
                right = _genre_freq(rows[candidate:end])
                gain = _cosine_distance(left, right)
                if gain > best_gain:
                    best_gain = gain
                    best_split = candidate
        if best_split is None or best_gain < min_gain:
            break
        splits.add(best_split)

    return sorted(splits)


def compute_genre_trends(user_id, top_n=3):
    """Detect periods of stable genre preference for a user's completed books.

    Returns a dict with periods, current-interest summary, and metadata.
    """
    raw_rows = db.execute(
        "SELECT id, book, date, genres FROM completed WHERE user_id = ?",
        user_id,
    )

    parsed = []
    missing_genres_completed = []
    for row in raw_rows:
        genres = _parse_genre_list(row.get("genres"))
        if not genres:
            missing_genres_completed.append(
                {"id": row["id"], "book": row["book"], "date": row.get("date")}
            )
            continue
        date_obj = parse_date_text(str(row.get("date") or ""))
        if date_obj is None:
            continue
        parsed.append(
            {
                "id": row["id"],
                "book": row["book"],
                "date": date_obj,
                "genres_list": genres,
            }
        )

    # Also include TBR / unfinished books missing genres, so the user can fix them all in one place.
    missing_other = []
    for category in ("tbr", "unfinished"):
        for row in db.execute(
            f"SELECT id, book, genres FROM {category} WHERE user_id = ?",
            user_id,
        ):
            if not _parse_genre_list(row.get("genres")):
                missing_other.append(
                    {"id": row["id"], "book": row["book"], "category": category}
                )

    missing_completed_sorted = sorted(
        missing_genres_completed, key=lambda r: (r["book"] or "").lower()
    )
    missing_other_sorted = sorted(
        missing_other, key=lambda r: (r["book"] or "").lower()
    )

    parsed.sort(key=lambda r: r["date"])
    splits = _find_change_points(parsed)

    periods = []
    for i in range(len(splits) - 1):
        start, end = splits[i], splits[i + 1]
        period_rows = parsed[start:end]
        if not period_rows:
            continue
        freq = _genre_freq(period_rows)
        top = sorted(freq.items(), key=lambda kv: (-kv[1], kv[0]))[:top_n]

        # Was this period preceded by a real reading break?
        gap_before_days = None
        if start > 0:
            gap = (period_rows[0]["date"] - parsed[start - 1]["date"]).days
            if gap >= 45:
                gap_before_days = gap

        periods.append(
            {
                "start_date": period_rows[0]["date"],
                "end_date": period_rows[-1]["date"],
                "book_count": len(period_rows),
                "top_genres": [{"genre": g, "count": c} for g, c in top],
                "all_genres_count": len(freq),
                "sample_books": [r["book"] for r in period_rows[:5]],
                "gap_before_days": gap_before_days,
            }
        )

    current_interest, window_info = _recent_interest_window(parsed, top_n=8)
    reread_suggestions = _suggest_rereads(
        parsed, current_interest, window_info, top_n=6
    )

    time_series = _bucket_genre_time_series(parsed, top_n=6)
    charts = _build_trend_charts(time_series) if time_series else None

    return {
        "total_books": len(parsed),
        "periods": periods,
        "current_interest": current_interest,
        "current_window": window_info,
        "reread_suggestions": reread_suggestions,
        "missing_completed": missing_completed_sorted,
        "missing_other": missing_other_sorted,
        "charts": charts,
    }


def _bucket_genre_time_series(parsed, top_n=6):
    """Bucket completed-book history into monthly or quarterly buckets and
    return per-bucket volumes plus per-genre counts for the top N genres.

    Adaptive granularity:
      - span ≤ 36 months  → monthly
      - else              → quarterly

    Returns None if there's nothing meaningful to chart.
    """
    if len(parsed) < 4:
        return None
    first = parsed[0]["date"]
    last = parsed[-1]["date"]
    months_span = (last.year - first.year) * 12 + (last.month - first.month) + 1
    unit = "month" if months_span <= 36 else "quarter"

    def bump_month(d):
        nm = d.month + 1
        ny = d.year + (nm - 1) // 12
        nm = ((nm - 1) % 12) + 1
        return date(ny, nm, 1)

    def bump_quarter(d):
        nm = d.month + 3
        ny = d.year + (nm - 1) // 12
        nm = ((nm - 1) % 12) + 1
        return date(ny, nm, 1)

    if unit == "month":
        start_bucket = date(first.year, first.month, 1)
        end_bucket = date(last.year, last.month, 1)
        step = bump_month
        def label_for(b):
            return {"full": b.strftime("%b %Y"), "short": b.strftime("%b '%y")}
        def index_of(d):
            return (d.year - start_bucket.year) * 12 + (d.month - start_bucket.month)
    else:
        sq = ((first.month - 1) // 3) * 3 + 1
        eq = ((last.month - 1) // 3) * 3 + 1
        start_bucket = date(first.year, sq, 1)
        end_bucket = date(last.year, eq, 1)
        step = bump_quarter
        def label_for(b):
            q = (b.month - 1) // 3 + 1
            return {"full": f"Q{q} {b.year}", "short": f"Q{q} '{str(b.year)[2:]}"}
        def index_of(d):
            sq_first = (start_bucket.month - 1) // 3
            dq = (d.month - 1) // 3
            return (d.year - start_bucket.year) * 4 + (dq - sq_first)

    buckets_dates = []
    cur = start_bucket
    while cur <= end_bucket:
        buckets_dates.append(cur)
        cur = step(cur)
    n_buckets = len(buckets_dates)
    if n_buckets < 2:
        return None

    volume = [0] * n_buckets
    overall_freq = {}
    per_bucket_genres = [dict() for _ in range(n_buckets)]
    for r in parsed:
        bi = index_of(r["date"])
        if bi < 0 or bi >= n_buckets:
            continue
        volume[bi] += 1
        for g in r["genres_list"]:
            overall_freq[g] = overall_freq.get(g, 0) + 1
            per_bucket_genres[bi][g] = per_bucket_genres[bi].get(g, 0) + 1

    top_genre_names = [
        g for g, _ in sorted(
            overall_freq.items(), key=lambda kv: (-kv[1], kv[0])
        )[:top_n]
    ]
    genre_series = [
        {
            "genre": g,
            "total": overall_freq[g],
            "points": [per_bucket_genres[i].get(g, 0) for i in range(n_buckets)],
        }
        for g in top_genre_names
    ]

    return {
        "unit": unit,
        "buckets": [label_for(b) for b in buckets_dates],
        "volume": volume,
        "max_volume": max(volume) if volume else 0,
        "genre_series": genre_series,
        "max_genre_value": max(
            (max(s["points"]) for s in genre_series), default=0
        ),
    }


GENRE_LINE_COLORS = [
    "#6B0F1A",  # deep red — house color
    "#b08968",  # tan
    "#3a6a78",  # teal
    "#8a4f7d",  # plum
    "#d7822a",  # amber
    "#4d6a3f",  # olive
]


def _y_ticks(max_val, plot_h, pad_top, count=4):
    """Generate evenly-spaced Y-axis ticks at "nice" round values.

    Picks the {1, 2, 2.5, 5} × 10^n step closest to the ideal (max/count),
    so the chart shows a sensible number of labels rather than 2 sparse ones.
    """
    if max_val <= 0:
        return [{"value": 0, "y": pad_top + plot_h}]
    raw_step = max_val / count
    magnitude = 10 ** max(0, int(math.log10(raw_step))) if raw_step >= 1 else 1
    best_step = magnitude
    best_diff = abs(magnitude - raw_step)
    for m in (1, 2, 2.5, 5, 10):
        cand = m * magnitude
        diff = abs(cand - raw_step)
        if diff < best_diff:
            best_diff = diff
            best_step = cand
    step = best_step
    ticks = []
    v = 0.0
    while v <= max_val + step / 2:
        y = pad_top + plot_h - (v / max_val) * plot_h
        if y < pad_top - 1:
            break
        value = int(v) if abs(v - round(v)) < 1e-9 else round(v, 1)
        ticks.append({"value": value, "y": round(y, 1)})
        v += step
    return ticks


def _build_trend_charts(ts):
    """Pre-compute SVG geometry for the trends-page line charts so the Jinja
    template stays declarative.
    """
    if not ts:
        return None
    n = len(ts["buckets"])
    if n < 2:
        return None

    width = 820
    height = 240
    pad_top, pad_right, pad_bottom, pad_left = 14, 14, 38, 38
    plot_w = width - pad_left - pad_right
    plot_h = height - pad_top - pad_bottom

    def x_for(i):
        return pad_left + (i / (n - 1)) * plot_w

    label_step = max(1, (n - 1) // 7)
    x_ticks = []
    for i, b in enumerate(ts["buckets"]):
        if i % label_step == 0 or i == n - 1:
            x_ticks.append({"x": round(x_for(i), 1), "label": b["short"]})

    def build_line(values, max_val):
        max_val = max_val or 1
        pts = []
        polyline = []
        for i, v in enumerate(values):
            x = x_for(i)
            y = pad_top + plot_h - (v / max_val) * plot_h
            polyline.append(f"{x:.1f},{y:.1f}")
            pts.append({"x": round(x, 1), "y": round(y, 1), "value": v})
        return {"polyline": " ".join(polyline), "points": pts}

    volume_line = build_line(ts["volume"], ts["max_volume"])
    vol_y_ticks = _y_ticks(ts["max_volume"], plot_h, pad_top)

    max_g = ts["max_genre_value"]
    genre_lines = []
    for idx, s in enumerate(ts["genre_series"]):
        line = build_line(s["points"], max_g)
        genre_lines.append(
            {
                "genre": s["genre"],
                "total": s["total"],
                "color": GENRE_LINE_COLORS[idx % len(GENRE_LINE_COLORS)],
                "polyline": line["polyline"],
                "points": line["points"],
            }
        )
    genre_y_ticks = _y_ticks(max_g, plot_h, pad_top)

    return {
        "unit_label": "month" if ts["unit"] == "month" else "quarter",
        "width": width,
        "height": height,
        "plot": {
            "top": pad_top,
            "left": pad_left,
            "right": width - pad_right,
            "bottom": pad_top + plot_h,
            "width": plot_w,
            "height": plot_h,
        },
        "x_ticks": x_ticks,
        "volume": {
            "polyline": volume_line["polyline"],
            "points": volume_line["points"],
            "max": ts["max_volume"],
            "y_ticks": vol_y_ticks,
        },
        "genres": {
            "lines": genre_lines,
            "max": max_g,
            "y_ticks": genre_y_ticks,
        },
        "buckets": ts["buckets"],
    }


def _recent_interest_window(parsed, top_n=8):
    """Pick a recent window of completed books and return genres that recur within it.

    Strategy: take the last ~30 reads (or 20% of the library, whichever is bigger,
    capped at 60). A genre only counts as a "current interest" if it appears in
    at least 3 books or 15% of the window — whichever is larger. This filters
    out one-off reads while staying responsive to recent shifts.

    Returns (genres_list, window_info | None). window_info has start/end dates
    and book_count.
    """
    if not parsed:
        return [], None
    n = len(parsed)
    # Adaptive window: at least 10, target ~20% of library, hard cap 60.
    window_size = min(max(10, n // 5), 60, n)
    if window_size < 5:
        # Too little data — fall back to whatever exists.
        window_size = n
    window = parsed[-window_size:]
    freq = _genre_freq(window)
    if not freq:
        return [], None
    threshold = max(3, int(round(len(window) * 0.15)))
    strong = [(g, c) for g, c in freq.items() if c >= threshold]
    # If the threshold filtered everything out (very diverse reader), fall back
    # to the raw top-N so something is still shown.
    if not strong:
        strong = sorted(freq.items(), key=lambda kv: (-kv[1], kv[0]))[:top_n]
    else:
        strong.sort(key=lambda kv: (-kv[1], kv[0]))
        strong = strong[:top_n]
    genres = [{"genre": g, "count": c} for g, c in strong]
    window_info = {
        "start_date": window[0]["date"],
        "end_date": window[-1]["date"],
        "book_count": len(window),
    }
    return genres, window_info


def _suggest_rereads(parsed, current_interest, window_info, top_n=6):
    """Suggest older completed books worth revisiting based on current taste.

    Scoring: how many genres a book shares with the current-interest set.
    Tie-break by oldest read date (longest since you last touched it).
    Excludes the recent window — those aren't "rereads", they're recent.
    """
    if not parsed or not current_interest or not window_info:
        return []
    interest_set = {item["genre"] for item in current_interest}
    if not interest_set:
        return []
    historical = parsed[: -window_info["book_count"]]
    if not historical:
        return []
    scored = []
    for r in historical:
        genres_set = set(r["genres_list"])
        matched = genres_set & interest_set
        if not matched:
            continue
        scored.append(
            {
                "score": len(matched),
                "book": r["book"],
                "id": r["id"],
                "date": r["date"],
                "matched_genres": sorted(matched),
            }
        )
    # Highest overlap first; tie-break by oldest (most due for revisit).
    scored.sort(key=lambda x: (-x["score"], x["date"]))
    return scored[:top_n]


@app.route("/trends", methods=["GET"])
def trends_view():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")
    data = compute_genre_trends(session["user_id"])
    return render_template("trends.html", trends=data, title="Genre Trends")


def _get_recent_interest_set(user_id):
    """Just the current-interest genre set for a user.

    Lighter than running the whole `compute_genre_trends` pipeline since we
    only need the set of genres the user is currently into.
    """
    rows = db.execute(
        "SELECT id, book, date, genres FROM completed WHERE user_id = ?",
        user_id,
    )
    parsed = []
    for row in rows:
        genres = _parse_genre_list(row.get("genres"))
        if not genres:
            continue
        date_obj = parse_date_text(str(row.get("date") or ""))
        if date_obj is None:
            continue
        parsed.append(
            {
                "id": row["id"],
                "book": row["book"],
                "date": date_obj,
                "genres_list": genres,
            }
        )
    parsed.sort(key=lambda r: r["date"])
    current_interest, _window = _recent_interest_window(parsed, top_n=8)
    return {item["genre"] for item in current_interest}, current_interest


CATEGORY_LABELS = {
    "tbr": "To Be Read",
    "unfinished": "Unfinished",
    "completed": "Completed",
}


def predict_next_book(user_id, exclude_ids=None):
    """Recommend a single book to read next, based on overlap with the
    user's current-interest genres.

    Eligible pool: every book EXCEPT completed books that were finished in
    the last 1 year. Among the rest, books that share more genres with the
    current-interest set score higher. TBR > unfinished > older completed
    is preferred via small category boosts. Returns one of the top
    candidates at random so the user can re-roll the suggestion.
    """
    interest_set, interest_list = _get_recent_interest_set(user_id)
    if not interest_set:
        return {
            "book": None,
            "reason": "no_interest",
            "interest": [],
        }

    today = date.today()
    one_year_ago = today - timedelta(days=365)
    exclude_ids = set(exclude_ids or [])
    category_boost = {"tbr": 1.0, "unfinished": 0.9, "completed": 0.6}

    candidates = []
    for cat in ("tbr", "unfinished", "completed"):
        rows = db.execute(
            f"SELECT id, book, genres, date FROM {cat} WHERE user_id = ?",
            user_id,
        )
        for r in rows:
            key = f"{cat}:{r['id']}"
            if key in exclude_ids:
                continue
            genres = set(_parse_genre_list(r.get("genres")))
            matched = genres & interest_set
            if not matched:
                continue

            # Filter: skip completed books finished in the last 12 months.
            if cat == "completed":
                d = parse_date_text(str(r.get("date") or ""))
                if d is not None and d >= one_year_ago:
                    continue

            score = len(matched) * category_boost[cat]
            candidates.append(
                {
                    "id": r["id"],
                    "key": key,
                    "book": r["book"],
                    "category": cat,
                    "category_label": CATEGORY_LABELS.get(cat, cat),
                    "score": round(score, 2),
                    "overlap": len(matched),
                    "matched_genres": sorted(matched),
                    "date": str(r.get("date") or ""),
                }
            )

    if not candidates:
        return {
            "book": None,
            "reason": "no_match",
            "interest": [item["genre"] for item in interest_list],
        }

    candidates.sort(key=lambda c: (-c["score"], -c["overlap"]))
    top = candidates[: min(len(candidates), 10)]
    pick = random.choice(top)

    return {
        "book": pick,
        "candidate_count": len(candidates),
        "interest": [item["genre"] for item in interest_list],
    }


@app.route("/api/predict_next_book", methods=["POST"])
def api_predict_next_book():
    if not session_user_exists():
        return {"error": "auth"}, 401
    payload = request.get_json(silent=True) or {}
    exclude = payload.get("exclude_ids") or []
    if not isinstance(exclude, list):
        exclude = []
    result = predict_next_book(session["user_id"], exclude_ids=exclude)
    return result


LANGUAGE_LABELS = {
    "chinese": "Chinese",
    "japanese": "Japanese",
    "korean": "Korean",
    "english": "English",
    "other": "Other",
}


def _detect_text_language(text):
    """Classify a short string (a genre name) into a coarse language bucket.

    Order matters: a Japanese genre often contains kanji, so detect kana
    first. Otherwise any Han characters fall back to Chinese.
    """
    if not text:
        return "other"
    if re.search(r"[぀-ゟ゠-ヿ]", text):
        return "japanese"
    if re.search(r"[가-힯]", text):
        return "korean"
    if re.search(r"[一-鿿㐀-䶿]", text):
        return "chinese"
    if re.search(r"[A-Za-z]", text):
        return "english"
    return "other"


def compute_genres(user_id):
    """Collect every genre tagged on the user's books with the books in each.

    Books are grouped per category so the page can show:
        Fantasy — 50 books (40 completed, 7 TBR, 3 unfinished)
            Completed: ...
            To Be Read: ...
            Unfinished: ...
    """
    genres_map = {}
    total_tagged = 0
    total_untagged = 0
    category_totals = {"completed": 0, "tbr": 0, "unfinished": 0}

    for category in ("completed", "tbr", "unfinished"):
        rows = db.execute(
            f"SELECT id, book, genres FROM {category} WHERE user_id = ? "
            "ORDER BY LOWER(book) ASC",
            user_id,
        )
        for r in rows:
            genres = _parse_genre_list(r.get("genres"))
            if not genres:
                total_untagged += 1
                continue
            total_tagged += 1
            category_totals[category] += 1
            for g in genres:
                bucket = genres_map.setdefault(
                    g, {"completed": [], "tbr": [], "unfinished": []}
                )
                bucket[category].append({"id": r["id"], "book": r["book"]})

    items = []
    language_totals = {}
    for g, by_cat in genres_map.items():
        c = len(by_cat["completed"])
        t = len(by_cat["tbr"])
        u = len(by_cat["unfinished"])
        lang = _detect_text_language(g)
        language_totals[lang] = language_totals.get(lang, 0) + 1
        items.append(
            {
                "genre": g,
                "total": c + t + u,
                "completed": by_cat["completed"],
                "tbr": by_cat["tbr"],
                "unfinished": by_cat["unfinished"],
                "completed_count": c,
                "tbr_count": t,
                "unfinished_count": u,
                "language": lang,
                "language_label": LANGUAGE_LABELS.get(lang, lang.title()),
            }
        )
    items.sort(key=lambda x: (-x["total"], x["genre"].lower()))

    max_total = items[0]["total"] if items else 0
    for it in items:
        it["bar_percent"] = (
            round(it["total"] * 100 / max_total, 1) if max_total else 0
        )

    # Only surface languages that actually appear, in a stable order.
    language_order = ("chinese", "japanese", "korean", "english", "other")
    languages_present = [
        {"key": k, "label": LANGUAGE_LABELS[k], "count": language_totals[k]}
        for k in language_order
        if language_totals.get(k)
    ]

    return {
        "total_distinct": len(items),
        "total_tagged": total_tagged,
        "total_untagged": total_untagged,
        "category_totals": category_totals,
        "languages": languages_present,
        "entries": items,
    }


@app.route("/genres", methods=["GET"])
def genres_view():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")
    data = compute_genres(session["user_id"])
    return render_template("genres.html", genres=data, title="Genres")


def compute_analytics(user_id):
    """Aggregate reading statistics for the analytics page."""
    completed_rows = db.execute(
        "SELECT id, book, date, days, reread, genres, series, status "
        "FROM completed WHERE user_id = ?",
        user_id,
    )
    tbr_rows = db.execute(
        "SELECT id, genres FROM tbr WHERE user_id = ?", user_id
    )
    unfinished_rows = db.execute(
        "SELECT id, genres FROM unfinished WHERE user_id = ?", user_id
    )

    completed_dated = []
    for r in completed_rows:
        parsed = parse_date_text(str(r.get("date") or ""))
        if parsed:
            r["_date"] = parsed
            completed_dated.append(r)

    total_completed = len(completed_rows)
    total_tbr = len(tbr_rows)
    total_unfinished = len(unfinished_rows)
    total_books = total_completed + total_tbr + total_unfinished
    completed_with_genres = 0
    completed_with_series = 0

    # Reading span (based on completed books with parseable dates).
    if completed_dated:
        sorted_by_date = sorted(completed_dated, key=lambda x: x["_date"])
        first_date = sorted_by_date[0]["_date"]
        last_date = sorted_by_date[-1]["_date"]
        span_days = (last_date - first_date).days + 1
    else:
        first_date = None
        last_date = None
        span_days = 0

    # Books per year.
    year_counts = {}
    monthly_all = {}
    for r in completed_dated:
        d = r["_date"]
        year_counts[d.year] = year_counts.get(d.year, 0) + 1
        key = (d.year, d.month)
        monthly_all[key] = monthly_all.get(key, 0) + 1
    years_sorted = sorted(year_counts.items())
    max_year_count = max((c for _, c in years_sorted), default=0)
    year_counts_list = [
        {
            "year": y,
            "count": c,
            "percent": round(c * 100 / max_year_count, 1) if max_year_count else 0,
        }
        for y, c in years_sorted
    ]
    year_genre_freq = {}
    for r in completed_dated:
        parsed_genres = _parse_genre_list(r.get("genres"))
        if not parsed_genres:
            continue
        year_bucket = year_genre_freq.setdefault(r["_date"].year, {})
        for g in parsed_genres:
            year_bucket[g] = year_bucket.get(g, 0) + 1
    year_genre_highlights = []
    for y, c in years_sorted:
        freq = year_genre_freq.get(y, {})
        total_year_genres = sum(freq.values())
        top_year_genres_raw = sorted(
            freq.items(), key=lambda kv: (-kv[1], kv[0])
        )[:3]
        year_genre_highlights.append(
            {
                "year": y,
                "count": c,
                "top_genres": [
                    {
                        "genre": g,
                        "count": count,
                        "percent": round(count * 100 / total_year_genres, 1)
                        if total_year_genres
                        else 0,
                    }
                    for g, count in top_year_genres_raw
                ],
                "has_genres": bool(freq),
            }
        )

    # Books per month — rolling 12-month window.
    today = date.today()
    months_window = []
    cursor = date(today.year, today.month, 1)
    for _ in range(12):
        months_window.append(cursor)
        if cursor.month == 1:
            cursor = date(cursor.year - 1, 12, 1)
        else:
            cursor = date(cursor.year, cursor.month - 1, 1)
    months_window.reverse()
    month_counts = []
    for m in months_window:
        c = monthly_all.get((m.year, m.month), 0)
        month_counts.append(
            {
                "label": m.strftime("%b %Y"),
                "short": m.strftime("%b"),
                "year": m.year,
                "count": c,
            }
        )
    max_month_count = max((m["count"] for m in month_counts), default=0)
    for m in month_counts:
        m["percent"] = (
            round(m["count"] * 100 / max_month_count, 1) if max_month_count else 0
        )

    # Genre frequencies (across completed books only — that's "what you've read").
    genre_freq = {}
    for r in completed_rows:
        parsed_genres = _parse_genre_list(r.get("genres"))
        if parsed_genres:
            completed_with_genres += 1
        if (r.get("series") or "").strip():
            completed_with_series += 1
        for g in parsed_genres:
            genre_freq[g] = genre_freq.get(g, 0) + 1
    total_genre_tags = sum(genre_freq.values())
    top_genres_raw = sorted(
        genre_freq.items(), key=lambda kv: (-kv[1], kv[0])
    )[:10]
    max_genre_count = top_genres_raw[0][1] if top_genres_raw else 0
    top_genres = [
        {
            "genre": g,
            "count": c,
            "percent": (
                round(c * 100 / total_genre_tags, 1) if total_genre_tags else 0
            ),
            "bar_percent": (
                round(c * 100 / max_genre_count, 1) if max_genre_count else 0
            ),
        }
        for g, c in top_genres_raw
    ]

    # Top series (by completed book count).
    series_freq = {}
    for r in completed_rows:
        s = (r.get("series") or "").strip()
        if s:
            series_freq[s] = series_freq.get(s, 0) + 1
    top_series_raw = sorted(
        series_freq.items(), key=lambda kv: (-kv[1], kv[0])
    )[:8]
    max_series_count = top_series_raw[0][1] if top_series_raw else 0
    top_series = [
        {
            "series": s,
            "count": c,
            "bar_percent": (
                round(c * 100 / max_series_count, 1) if max_series_count else 0
            ),
        }
        for s, c in top_series_raw
    ]

    # Reading pace from `days` column.
    days_vals = [
        (r.get("days") or 0) for r in completed_rows if (r.get("days") or 0) > 0
    ]
    avg_days = None
    median_days = None
    fastest_book = None
    slowest_book = None
    if days_vals:
        avg_days = round(sum(days_vals) / len(days_vals), 1)
        sorted_days = sorted(days_vals)
        mid = len(sorted_days) // 2
        if len(sorted_days) % 2 == 1:
            median_days = sorted_days[mid]
        else:
            median_days = round(
                (sorted_days[mid - 1] + sorted_days[mid]) / 2, 1
            )
        with_days = [
            r for r in completed_rows if (r.get("days") or 0) > 0
        ]
        fastest = min(with_days, key=lambda r: r["days"])
        slowest = max(with_days, key=lambda r: r["days"])
        fastest_book = {"book": fastest["book"], "days": fastest["days"]}
        slowest_book = {"book": slowest["book"], "days": slowest["days"]}

    avg_per_month = None
    if span_days > 0 and total_completed > 0:
        months_span = max(span_days / 30.4375, 1.0)
        avg_per_month = round(total_completed / months_span, 2)

    # Reread stats.
    reread_total = sum((r.get("reread") or 0) for r in completed_rows)
    reread_books = sum(
        1 for r in completed_rows if (r.get("reread") or 0) > 0
    )
    top_rereads = sorted(
        [r for r in completed_rows if (r.get("reread") or 0) > 0],
        key=lambda r: (-(r.get("reread") or 0), r.get("book") or ""),
    )[:5]
    top_rereads = [
        {"book": r["book"], "reread": r["reread"]} for r in top_rereads
    ]

    # Status breakdown — overall library distribution.
    status_breakdown = []
    status_colors = {
        "completed": "#6B0F1A",
        "tbr": "#b08968",
        "unfinished": "#8a7c75",
    }
    running_percent = 0.0
    status_items = [
        ("Completed", total_completed, "completed"),
        ("To Be Read", total_tbr, "tbr"),
        ("Unfinished", total_unfinished, "unfinished"),
    ]
    for idx, (label, n, cls) in enumerate(status_items):
        pct = round(n * 100 / total_books, 1) if total_books else 0
        start_pct = round(running_percent, 1)
        running_percent += n * 100 / total_books if total_books else 0
        end_pct = 100.0 if idx == len(status_items) - 1 and total_books else round(running_percent, 1)
        status_breakdown.append(
            {
                "label": label,
                "count": n,
                "percent": pct,
                "key": cls,
                "color": status_colors[cls],
                "start_pct": start_pct,
                "end_pct": end_pct,
            }
        )

    completion_rate = round(total_completed * 100 / (total_unfinished + total_completed), 1) if total_books else 0
    genre_coverage = round(completed_with_genres * 100 / total_completed, 1) if total_completed else 0
    series_coverage = round(completed_with_series * 100 / total_completed, 1) if total_completed else 0
    reread_share = round(reread_books * 100 / total_completed, 1) if total_completed else 0

    # Busiest highlights.
    busiest_year = None
    if year_counts:
        y, c = max(year_counts.items(), key=lambda kv: kv[1])
        busiest_year = {"year": y, "count": c}
    busiest_month = None
    if monthly_all:
        (y, mo), c = max(monthly_all.items(), key=lambda kv: kv[1])
        busiest_month = {
            "label": date(y, mo, 1).strftime("%B %Y"),
            "count": c,
        }

    # How many completed books have a parseable date (data quality hint).
    completed_with_date = len(completed_dated)
    completed_without_date = total_completed - completed_with_date

    # Build the same Reading-evolution line charts the Trends page uses, so
    # the PDF report can show them too. We need dated completions that also
    # have at least one genre tag.
    chart_rows = []
    for r in completed_dated:
        genres_list = _parse_genre_list(r.get("genres"))
        if not genres_list:
            continue
        chart_rows.append(
            {
                "id": r["id"],
                "book": r["book"],
                "date": r["_date"],
                "genres_list": genres_list,
            }
        )
    chart_rows.sort(key=lambda x: x["date"])
    time_series = _bucket_genre_time_series(chart_rows, top_n=6)
    evolution_charts = _build_trend_charts(time_series) if time_series else None

    return {
        "totals": {
            "completed": total_completed,
            "tbr": total_tbr,
            "unfinished": total_unfinished,
            "all": total_books,
            "rereads_total": reread_total,
            "reread_books": reread_books,
            "completed_with_date": completed_with_date,
            "completed_without_date": completed_without_date,
            "completed_with_genres": completed_with_genres,
            "completed_with_series": completed_with_series,
            "distinct_genres": len(genre_freq),
            "distinct_series": len(series_freq),
        },
        "ratios": {
            "completion_rate": completion_rate,
            "genre_coverage": genre_coverage,
            "series_coverage": series_coverage,
            "reread_share": reread_share,
        },
        "span": {
            "start_date": first_date,
            "end_date": last_date,
            "days": span_days,
            "years": round(span_days / 365.25, 1) if span_days else 0,
            "months": round(span_days / 30.4375, 1) if span_days else 0,
        },
        "year_counts": year_counts_list,
        "year_genre_highlights": year_genre_highlights,
        "month_counts": month_counts,
        "top_genres": top_genres,
        "top_series": top_series,
        "pace": {
            "avg_days": avg_days,
            "median_days": median_days,
            "fastest": fastest_book,
            "slowest": slowest_book,
            "avg_per_month": avg_per_month,
        },
        "top_rereads": top_rereads,
        "status_breakdown": status_breakdown,
        "busiest_year": busiest_year,
        "busiest_month": busiest_month,
        "evolution_charts": evolution_charts,
    }


@app.route("/analytics", methods=["GET"])
def analytics_view():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")
    data = compute_analytics(session["user_id"])
    return render_template("analytics.html", stats=data, title="Analytics")


@app.route("/analytics/details", methods=["GET"])
def analytics_details_view():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")
    data = compute_analytics(session["user_id"])
    generated_on = date.today().strftime("%d %b %Y")
    html = render_template(
        "analytics_report_pdf.html",
        stats=data,
        generated_on=generated_on,
        title="Detailed Analytics Report",
    )

    try:
        pdf_bytes = render_analytics_pdf(html)
    except Exception:
        app.logger.exception("Unable to generate analytics PDF")
        return html

    response = Response(pdf_bytes, mimetype="application/pdf")
    response.headers["Content-Disposition"] = (
        'inline; filename="reading-records-analytics-report.pdf"'
    )
    return response


def _playwright_python_executable():
    env_python = os.environ.get("PLAYWRIGHT_PYTHON")
    if env_python:
        return env_python
    candidate = Path.home() / "miniforge3" / "bin" / "python"
    if candidate.exists():
        return str(candidate)
    return sys.executable


def render_analytics_pdf(html):
    helper_script = Path(BASE_DIR) / "render_analytics_report_pdf.py"
    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        html_path = tmpdir_path / "analytics-report.html"
        pdf_path = tmpdir_path / "analytics-report.pdf"
        html_path.write_text(html, encoding="utf-8")

        result = subprocess.run(
            [_playwright_python_executable(), str(helper_script), str(html_path), str(pdf_path)],
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            stderr = (result.stderr or "").strip()
            stdout = (result.stdout or "").strip()
            details = stderr or stdout or "Unknown PDF export error"
            raise RuntimeError(details)

        return pdf_path.read_bytes()


@app.route("/api/update_genres/<category>/<int:book_id>", methods=["POST"])
def api_update_genres(category, book_id):
    if not session_user_exists():
        return {"error": "auth"}, 401
    if category not in BOOK_PAGES:
        return {"error": "invalid category"}, 400
    data = request.get_json() or {}
    genres = (data.get("genres") or "").strip()

    existing = db.execute(
        f"SELECT id FROM {category} WHERE id = ? AND user_id = ? LIMIT 1",
        book_id, session["user_id"],
    )
    if not existing:
        return {"error": "not found"}, 404

    db.execute(
        f"UPDATE {category} SET genres = ? WHERE id = ? AND user_id = ?",
        genres, book_id, session["user_id"],
    )
    return {"ok": True, "genres": genres}


@app.route("/series", methods=["GET", "POST"])
def series_view():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")

    series_map = {}
    # Natural sort helper: splits on digit groups so numeric parts sort numerically
    def _natural_key(s):
        parts = re.split(r"(\d+)", (s or "").lower())
        return [int(p) if p.isdigit() else p for p in parts]
    category_order = ("completed", "unfinished", "tbr")
    for category in category_order:
        within_order = "date ASC, id ASC" if category == "completed" else "date DESC, id DESC"
        rows = db.execute(
            f"SELECT id, book, series, status, date FROM {category} "
            "WHERE user_id = ? AND series IS NOT NULL AND TRIM(series) != '' "
            f"ORDER BY series, {within_order}",
            session["user_id"],
        )
        for row in rows:
            key = row["series"].strip()
            row["category"] = category
            series_map.setdefault(key, []).append(row)

    series_list = sorted(series_map.items(), key=lambda kv: _natural_key(kv[0]))

    # Handle min/max book count filters
    min_books = None
    max_books = None
    selected_min = ""
    selected_max = ""
    if request.method == "POST":
        if "clear" in request.form:
            # ignore filters
            pass
        else:
            try:
                mb = (request.form.get("min_books") or "").strip()
                if mb != "":
                    min_books = int(mb)
                    selected_min = mb
            except ValueError:
                min_books = None
            try:
                xb = (request.form.get("max_books") or "").strip()
                if xb != "":
                    max_books = int(xb)
                    selected_max = xb
            except ValueError:
                max_books = None

    if min_books is not None or max_books is not None:
        filtered = []
        for name, books in series_list:
            cnt = len(books)
            if min_books is not None and cnt < min_books:
                continue
            if max_books is not None and cnt > max_books:
                continue
            filtered.append((name, books))
        series_list = filtered
    total_books = sum(len(books) for _, books in series_list)
    return render_template(
        "series.html",
        series_list=series_list,
        total_series=len(series_list),
        total_books=total_books,
        selected_min=selected_min,
        selected_max=selected_max,
    )


@app.route("/search", methods=["GET", "POST"])
def search():
    if request.method == "POST":
        book = request.form.get("search", "").lower()
        exists = db.execute("SELECT * FROM combined WHERE user_id = ? AND book LIKE ?", session["user_id"], '%' + book + '%')
        if not exists:
            flash("No books with similar names found! Try a different keyword? 🤔")
            return redirect("/home")

        results = []
        categories = {row["page"] for row in exists}
        for category in categories:
            rows = db.execute(
                f"SELECT * FROM {category} WHERE user_id = ? AND book LIKE ?",
                session["user_id"],
                '%' + book + '%',
            )
            for r in rows:
                r["category"] = category
                results.append(r)
        # Sort results by date (newest first). Dates are stored as YYYY-MM-DD strings,
        # so string-sort works; fall back to empty string for missing dates.
        results.sort(key=lambda r: (r.get("date") or ""), reverse=True)
        return render_template("search.html", results=results, search=book)
    return redirect("/home")



@app.route("/", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        username = request.form.get("username")
        password = request.form.get("password")
        user = db.execute("SELECT * FROM users WHERE username = ?", username)
        if len(user) > 0 and check_password_hash(user[0]["hash"], password):
            session["user_id"] = user[0]["id"]
            return redirect("/home")
        else:
            flash("No user found!")
            return redirect("/")
    else:
        return render_template("login.html")
    
@app.route("/logout")
def logout():
    session.clear()
    return redirect("/")

@app.route("/register", methods=["GET", "POST"])
def register():
    if request.method == "POST":
        username = request.form.get("username")
        password = request.form.get("password")
        confirmation = request.form.get("confirmation")
        exists = db.execute("SELECT * FROM users WHERE username = ?", username)
        if not username or not password or not confirmation:
            flash("Must fill in all fields")
        elif len(exists) > 0:
            flash("Username exists")
        elif password != confirmation:
            flash("Passwords do not match")
        else:
            hash = generate_password_hash(password)
            db.execute("INSERT INTO users (username, hash, date) VALUES (?, ?, ?)", username, hash, today)
            id = db.execute("SELECT id FROM users WHERE username = ?", username)
            session["user_id"] = id[0]["id"]
            return redirect("/home")
        return redirect("/register")
    else:
        return render_template("register.html")
    
