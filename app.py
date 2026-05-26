from flask import Flask, redirect, session, render_template, request, flash, url_for
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


def query_books_with_filters(category, user_id, status_filter=None, existence_filter=None):
    query = f"SELECT * FROM {category} WHERE user_id = ?"
    params = [user_id]
    if status_filter:
        query += " AND status = ?"
        params.append(status_filter)
    if existence_filter in ("genres", "series", "notes"):
        query += f" AND {existence_filter} IS NOT NULL AND {existence_filter} != ''"
        query += f" ORDER BY {existence_filter}"
    else:
        query += " ORDER BY date DESC, id DESC"
    return db.execute(query, *params)


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

    Qidian aggressively challenges headless browsers — many requests come back
    as 202 with an empty body. The handler tries a couple of common selectors
    and returns an empty list when the challenge wins.
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
                page = browser.new_page(user_agent=DESKTOP_UA, locale="zh-CN")
                response = page.goto(url, wait_until="domcontentloaded", timeout=20000)
                if response is not None and response.status >= 400:
                    return []
                page.wait_for_timeout(5000)
                tags = page.evaluate(
                    """() => {
                        const out = [];
                        const selectors = [
                            '.crumb a',
                            '.book-info-detail .tag a',
                            '.book-information .crumb a',
                            '.all-attr a',
                            '.book-attribute .all-attr a',
                            'a[href*="chanId"]',
                        ];
                        for (const sel of selectors) {
                            document.querySelectorAll(sel).forEach(el => {
                                const text = (el.innerText || '').trim();
                                if (text) out.push(text);
                            });
                            if (out.length) break;
                        }
                        return out;
                    }"""
                )
            finally:
                browser.close()
    except Exception:
        return []

    drop = {"首页", "全部作品", "完本作品", "网络小说", "起点中文网", "免费小说"}
    seen = set()
    out = []
    for t in tags:
        if not t or t in drop:
            continue
        key = t.casefold()
        if key in seen:
            continue
        seen.add(key)
        out.append(t)
    return out[:5]


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
        steps = (_jjwxc_step, _qidian_step)
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

    notes.extend([n.strip() for n in re.findall(r"\*(.*?)\*", text) if n.strip()])
    notes.extend([n.strip() for n in re.findall(r"[\{｛](.*?)[\}｝]", text) if n.strip()])

    if "✔" in text:
        notes.append("Favorite")
    if re.search(r"#nice\b", text, flags=re.IGNORECASE):
        notes.append("Would recommend to others")

    author_match = re.search(r"作者[:：]\s*([^\]\)）\}]+)", text)
    if author_match:
        notes.append(f"Author disambiguation: {author_match.group(1).strip()}")

    series_match = re.search(r"}\s*(\d+)", text)
    if series_match:
        series = f"Series {series_match.group(1)}"

    return notes, series


def clean_freeform_note(text):
    cleaned = re.sub(r"\*(.*?)\*", r"\1", text).strip()
    cleaned = re.sub(r"[\{｛](.*?)[\}｝]", r"\1", cleaned)
    cleaned = cleaned.replace("✔️", "").replace("✔", "")
    cleaned = re.sub(r"#nice\b", "", cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r"}\s*\d+", "", cleaned)
    cleaned = re.sub(r"作者[:：]\s*[^\]\)）\}]+", "", cleaned)
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
    common_notes, series = parse_common_metadata(line)

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

    common_notes, series = parse_common_metadata(line)
    notes = []
    notes.extend(title_notes)
    notes.extend(common_notes)

    return {
        "book": title,
        "notes": notes,
        "series": series,
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

    common_notes, series = parse_common_metadata(cleaned_line)
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
                "UPDATE completed SET reread = ?, notes = ? WHERE id = ? AND user_id = ?",
                previous.get("reread", 0),
                previous.get("notes"),
                row_id,
                user_id,
            )
        elif action_type == "update_unfinished":
            previous = action.get("previous", {})
            db.execute(
                "UPDATE unfinished SET status = ?, notes = ?, series = ?, date = ? WHERE id = ? AND user_id = ?",
                previous.get("status"),
                previous.get("notes"),
                previous.get("series"),
                previous.get("date"),
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

        key = normalize_book_key(entry["book"])
        if key in aggregated:
            existing = aggregated[key]
            if entry["date"] and (existing["date"] is None or entry["date"] < existing["date"]):
                existing["date"] = entry["date"]
            existing["notes"].extend(entry["notes"])
            existing["reread"] += 1 + entry["reread"]
            if not existing["series"] and entry["series"]:
                existing["series"] = entry["series"]
        else:
            aggregated[key] = entry

    for entry in aggregated.values():
        existing = find_existing_book_row("completed", user_id, entry["book"], "id, reread, notes, book")
        entry_notes = merge_notes(entry["notes"])

        if existing:
            increment = entry["reread"] if entry["reread"] > 0 else 1
            merged = merge_notes([existing[0]["notes"], entry_notes])
            undo_actions.append(
                {
                    "action": "update_completed",
                    "table": "completed",
                    "id": existing[0]["id"],
                    "previous": {
                        "reread": existing[0]["reread"],
                        "notes": existing[0]["notes"],
                    },
                }
            )
            db.execute(
                "UPDATE completed SET reread = ?, notes = ? WHERE id = ? AND user_id = ?",
                existing[0]["reread"] + increment,
                merged,
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
            "INSERT INTO completed (user_id, book, date, days, notes, reread, status, series) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
            user_id,
            entry["book"],
            completed_date,
            days,
            entry_notes,
            entry["reread"],
            "Finished",
            entry["series"],
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
        if key not in aggregated:
            entry["status"] = current_status
            aggregated[key] = entry

    for entry in aggregated.values():
        existing = find_existing_book_row("tbr", user_id, entry["book"], "id, book")
        if existing:
            continue

        notes_text = merge_notes(entry["notes"])
        book_date = date.today()
        book_id = db.execute(
            "INSERT INTO tbr (user_id, book, status, date, notes, series) VALUES (?, ?, ?, ?, ?, ?)",
            user_id,
            entry["book"],
            entry.get("status", "Uncompleted"),
            book_date,
            notes_text,
            entry["series"],
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
        aggregated[key] = entry

    for entry in aggregated.values():
        existing = find_existing_book_row("unfinished", user_id, entry["book"], "id, notes, status, series, date, book")
        notes_text = merge_notes(entry["notes"])
        book_date = date.today()

        if existing:
            merged = merge_notes([existing[0]["notes"], notes_text])
            previous_row = db.execute(
                "SELECT status, notes, series, date, book FROM unfinished WHERE id = ? AND user_id = ? LIMIT 1",
                existing[0]["id"],
                user_id,
            )
            previous_combined = db.execute(
                "SELECT date, book FROM combined WHERE user_id = ? AND page = 'unfinished' AND id = ? LIMIT 1",
                user_id,
                existing[0]["id"],
            )
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
                        "combined_date": previous_combined[0]["date"] if previous_combined else None,
                        "combined_book": previous_combined[0]["book"] if previous_combined else None,
                    },
                }
            )
            db.execute(
                "UPDATE unfinished SET status = ?, notes = ?, series = ?, date = ? WHERE id = ? AND user_id = ?",
                entry["status"],
                merged,
                entry["series"],
                book_date,
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
            "INSERT INTO unfinished (user_id, book, date, notes, status, series) VALUES (?, ?, ?, ?, ?, ?)",
            user_id,
            entry["book"],
            book_date,
            notes_text,
            entry["status"],
            entry["series"],
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
        f"INSERT INTO {new} (user_id, book, date, notes, genres, status, series) VALUES (?, ?, ?, ?, ?, ?, ?)",
        session["user_id"],
        book[0]["book"],
        today,
        book[0]["notes"],
        book[0]["genres"],
        book[0]["status"],
        book[0]["series"],
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

    if not (status_filter or existence_filter):
        stored = session.get("filters", {}).get(page, {})
        status_filter = stored.get("status_filter", "")
        existence_filter = stored.get("existence_filter", "")

    if status_filter or existence_filter:
        candidates = query_books_with_filters(page, session["user_id"], status_filter, existence_filter)
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

    if request.method == "POST":
        # Clear filters when requested
        if "clear" in request.form:
            session.setdefault("filters", {}).pop(category, None)
            status_filter = ""
            existence_filter = ""
        else:
            # Merge new filters with saved ones so selections stack
            new_status = request.form.get("status_filter")
            new_exist = request.form.get("filter")

            status_filter = (new_status.strip() if new_status is not None else saved_filters.get("status_filter", ""))
            existence_filter = (new_exist.strip() if new_exist is not None else saved_filters.get("existence_filter", ""))

            session.setdefault("filters", {})[category] = {
                "status_filter": status_filter,
                "existence_filter": existence_filter,
            }
    else:
        status_filter = saved_filters.get("status_filter", "")
        existence_filter = saved_filters.get("existence_filter", "")

    if status_filter or existence_filter:
        books = query_books_with_filters(category, session["user_id"], status_filter, existence_filter)
    else:
        books = db.execute(
            f"SELECT * FROM {category} WHERE user_id = ? ORDER BY date DESC, id DESC",
            session["user_id"],
        )

    return render_template(
        template_name,
        books=books,
        random=session.get("selected", []),
        selected_status=status_filter,
        selected_existence=existence_filter,
        status_options=get_status_options(category, session["user_id"]),
    )


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


@app.route("/update/<category>/<int:book_id>", methods=["POST"])
def update_book(category, book_id):
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")

    if category not in BOOK_PAGES:
        flash("Invalid category.")
        return redirect("/home")

    book_name = (request.form.get("book") or "").strip()
    status = (request.form.get("status") or "").strip()
    genres = (request.form.get("genres") or "").strip()
    series = (request.form.get("series") or "").strip()
    notes = (request.form.get("notes") or "").strip()

    if not book_name:
        flash("Book name cannot be empty.")
        return redirect(f"/{category}#book-{book_id}")

    existing = db.execute(
        f"SELECT id FROM {category} WHERE id = ? AND user_id = ? LIMIT 1",
        book_id, session["user_id"],
    )
    if not existing:
        flash("That book no longer exists.")
        return redirect(f"/{category}")

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

    flash("Book updated.")
    return redirect(f"/{category}#book-{book_id}")


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


def _find_change_points(rows, min_period=3, max_periods=5, min_gain=0.25):
    """Binary segmentation on the genre signal.

    Returns sorted list of split indices including 0 and len(rows), so
    consecutive pairs define each period.
    """
    n = len(rows)
    if n < 2 * min_period:
        return [0, n]

    splits = [0, n]
    while len(splits) - 1 < max_periods:
        best_split = None
        best_gain = 0.0
        for i in range(len(splits) - 1):
            start, end = splits[i], splits[i + 1]
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
        splits.append(best_split)
        splits.sort()
    return splits


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
        periods.append(
            {
                "start_date": period_rows[0]["date"],
                "end_date": period_rows[-1]["date"],
                "book_count": len(period_rows),
                "top_genres": [{"genre": g, "count": c} for g, c in top],
                "all_genres_count": len(freq),
                "sample_books": [r["book"] for r in period_rows[:5]],
            }
        )

    current = periods[-1]["top_genres"] if periods else []

    return {
        "total_books": len(parsed),
        "periods": periods,
        "current_interest": current,
        "missing_completed": missing_completed_sorted,
        "missing_other": missing_other_sorted,
    }


@app.route("/trends", methods=["GET"])
def trends_view():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")
    data = compute_genre_trends(session["user_id"])
    return render_template("trends.html", trends=data, title="Genre Trends")


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
    status_items = list((
        ("Completed", total_completed, "completed"),
        ("To Be Read", total_tbr, "tbr"),
        ("Unfinished", total_unfinished, "unfinished"),
    ))
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

    completion_rate = round(total_completed * 100 / total_books, 1) if total_books else 0
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
    }


@app.route("/analytics", methods=["GET"])
def analytics_view():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")
    data = compute_analytics(session["user_id"])
    return render_template("analytics.html", stats=data, title="Analytics")


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
    
