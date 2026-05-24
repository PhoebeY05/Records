from flask import Flask, redirect, session, render_template, request, flash, url_for
from flask_session import Session
from cs50 import SQL
from werkzeug.security import check_password_hash, generate_password_hash
from datetime import date, datetime, timedelta
from html import unescape
from html.parser import HTMLParser
import io
import random
import re
import os
import subprocess
import tempfile
import xml.etree.ElementTree as ET
import zipfile


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

    # Strict format: day full-month-name year (e.g. 21 March 2026)
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


UNFINISHED_CHAPTER_PATTERNS = [
    re.compile(r"\bchapter\b\s*[^\s<>()\[\]{}]+", flags=re.IGNORECASE),
    re.compile(r"\bvolume\b\s*[^\s<>()\[\]{}]+", flags=re.IGNORECASE),
    re.compile(r"(?:\d+|[一二三四五六七八九十百千零〇两]+)章", flags=re.IGNORECASE),
    re.compile(r"(?:\d+|[一二三四五六七八九十百千零〇两]+)页", flags=re.IGNORECASE),
]


def extract_unfinished_chapter(text):
    matches = [match for pattern in UNFINISHED_CHAPTER_PATTERNS if (match := pattern.search(text))]
    if not matches:
        return None, text

    match = max(matches, key=lambda item: item.start())
    unread_chapter = match.group(0).strip().rstrip(".,;:!?")

    prefix = re.sub(r"[\s<\(\[\{（【｛]+$", "", text[:match.start()])
    suffix = re.sub(r"^[\s>\)\]\}）】｝]+", "", text[match.end():])
    cleaned_text = re.sub(r"\s+", " ", f"{prefix} {suffix}").strip()
    return unread_chapter, cleaned_text


def parse_unfinished_line(line):
    cleaned_line = re.sub(r"\(\s*haven['’]?t read\s*\)", "", line, flags=re.IGNORECASE).strip()

    if not has_book_name_prefix(cleaned_line):
        return None

    unread_chapter, title_source = extract_unfinished_chapter(cleaned_line)
    status = "Unfinished"
    if unread_chapter:
        extra = f"Haven't read {unread_chapter}"
        source_text = title_source
    else:
        extra = ""
        source_text = cleaned_line

    title, title_notes = parse_title(title_source)
    if not title:
        return None

    common_notes, series = parse_common_metadata(source_text)
    notes = []
    notes.extend(title_notes)
    notes.extend(common_notes)
    if extra:
        notes.append(extra)

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
                return render_template("home.html", completed=completed, unfinished=unfinished, tbr=tbr, current_year=current_year)
                
        else:
            duration = request.form.get("duration")
            
            if duration == "day":
                day = db.execute("SELECT * FROM combined WHERE date = ? AND user_id = ?", today, session["user_id"])
                return render_template("home.html", day=day, option="day", current_year=current_year)
            elif duration == "week":
                week = db.execute("SELECT * FROM combined WHERE strftime('%W', date)  = ? AND user_id = ?", today.strftime("%W"), session["user_id"])
                return render_template("home.html",week=week,option="week", current_year=current_year)
            elif duration == "month":
                month = db.execute("SELECT * FROM combined WHERE strftime('%m', date) = ? AND user_id = ?", '%02d' % today.month, session["user_id"])
                return render_template("home.html", month=month,option="month", current_year=current_year)
            else:
                flash("Submission failed! No valid options were selected.")
                return redirect("/home")
       
    else:
        return render_template("home.html", current_year=current_year)

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
    all = db.execute(f"SELECT * FROM {page}")
    random.shuffle(all)
    if all == []:
        session["selected"] = {"book": "No Books Found", "status":"", "genres": "", "notes":"","series":""}
    else:
        session["selected"] = all[0]
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

    status_filter = (request.form.get("status_filter") or "").strip() if request.method == "POST" else ""
    existence_filter = (request.form.get("filter") or "").strip() if request.method == "POST" else ""

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


@app.route("/series")
def series_view():
    if not session_user_exists():
        session.clear()
        flash("Your session is no longer valid. Please log in again.")
        return redirect("/")

    series_map = {}
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

    series_list = sorted(series_map.items(), key=lambda kv: kv[0].lower())
    total_books = sum(len(books) for _, books in series_list)
    return render_template(
        "series.html",
        series_list=series_list,
        total_series=len(series_list),
        total_books=total_books,
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
    
