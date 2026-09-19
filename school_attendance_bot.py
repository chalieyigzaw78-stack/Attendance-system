"""
School Attendance Bot (python-telegram-bot)
-----------------------------------------------
A Telegram bot for schools: teachers take attendance from their phone,
parents get notified instantly if their child is marked absent/late, and
the whole school structure (buildings, grades, sections, students,
teachers) is built up THROUGH the bot -- nothing needs to be known or
configured in advance.

RUNS 24/7 WHEN DEPLOYED (e.g. Render, Railway):
  - Opens a tiny HTTP server on $PORT so free "Web Service" hosting tiers
    (which require something listening on a port) accept it, even though
    the bot itself only needs Telegram long-polling.
  - Build Command:  pip install -r requirements.txt
  - Start Command:  python school_attendance_bot.py

PERSISTENT STORAGE:
  If DATABASE_URL is set (a Postgres connection string, e.g. from a free
  Neon.tech database), the bot uses that -- data survives restarts and
  redeploys. If DATABASE_URL is NOT set, it falls back to a local SQLite
  file (DB_PATH) for easy local testing, but that file gets WIPED on most
  free hosting redeploys. For a real deployment, set DATABASE_URL.

  Set TG_BOT_TOKEN and DATABASE_URL as real environment variables on your
  host (e.g. Render's Environment tab) rather than committing a .env file
  to your repo -- this keeps your credentials out of git history.

SETUP:
  pip install -r requirements.txt
  Add to .env (local only, never commit this file) or your platform's
  environment variables (deployed):
    TG_BOT_TOKEN=       (from @BotFather)
    DATABASE_URL=       (optional but recommended for deployment -- a
                          Postgres connection string, e.g. from Neon.tech's
                          free tier: postgres://user:pass@host/dbname)
    DB_PATH=./attendance.db   (only used when DATABASE_URL is not set)

FIRST RUN:
  The very first person to send /start becomes the first admin
  automatically. After that, only admins can add other admins.

ADMIN COMMANDS:
  /addadmin <telegram_id>
      Grant admin rights to another Telegram user ID.

  /addclass <Building > Grade > Section>
      Creates the building/grade/section if they don't exist yet.
      Example: /addclass Main Campus > Grade 9 > Section A

  /addstudent <Building > Grade > Section> | <Student Full Name>
      Adds a single student to an EXISTING class path. Returns a parent
      link code -- give this to the student's parent/guardian.
      Example: /addstudent Main Campus > Grade 9 > Section A | Selam Bekele

  /addstudents <Building > Grade > Section>
      Bulk-add students to an EXISTING class. After running this, upload
      an Excel (.xlsx), CSV (.csv), or PDF (.pdf) file with one student
      name per row/line. The bot adds them all and replies with every
      parent link code.

  /addteacher <numeric telegram id> <Teacher Name>
      Registers a teacher (they still need to /start the bot themselves
      at least once so their Telegram account is known to it).

  /assignteacher <numeric telegram id> <Building > Grade > Section>
      Gives a teacher access to take attendance for that class.

  /listclasses
      Shows the full building -> grade -> section tree.

  /liststudents <Building > Grade > Section>
      Lists students (and their parent-link status) in a class.

  /studentcode <Building > Grade > Section> | <Student Name>
      Re-shows a student's parent link code.

  /absentees [YYYY-MM-DD]
      Lists everyone marked absent/late school-wide for a date
      (defaults to today).

TEACHER COMMANDS:
  /myclasses
      Shows the classes this teacher is assigned to as tappable buttons.
      Tapping a class immediately starts attendance for it -- no typing
      needed. Teachers also see a persistent "📋 My Classes" button after
      /start, which does the same thing.

  /attendance <Building > Grade > Section>
      Starts roll call directly by typing the class path: one message, a
      button per student (defaults to Present), tap to cycle Present ->
      Absent -> Late, then Submit.

PARENT / GUARDIAN:
  /link <code>
      Links this Telegram chat to a student using the code the school
      gave you. From then on, you're notified automatically whenever
      that student is marked absent or late.

  You can also just tap a t.me/<bot>?start=<code> link if the school
  shares one directly.
"""

import os
import io
import csv
import sqlite3
import secrets
import threading
from datetime import datetime, date
from http.server import BaseHTTPRequestHandler, HTTPServer
from dotenv import load_dotenv
from telegram import (
    Update,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    ReplyKeyboardMarkup,
)
from telegram.ext import (
    Application,
    CommandHandler,
    CallbackQueryHandler,
    MessageHandler,
    filters,
    ContextTypes,
)

load_dotenv()

BOT_TOKEN = os.environ["TG_BOT_TOKEN"]
DB_PATH = os.environ.get("DB_PATH", "./attendance.db")
DATABASE_URL = os.environ.get("DATABASE_URL", "").strip()
USE_POSTGRES = bool(DATABASE_URL)

if USE_POSTGRES:
    import psycopg2
    import psycopg2.extras

STATUS_CYCLE = ["present", "absent", "late"]
STATUS_EMOJI = {"present": "✅", "absent": "❌", "late": "🕒"}

MY_CLASSES_LABEL = "📋 My Classes"
TEACHER_MENU = ReplyKeyboardMarkup([[MY_CLASSES_LABEL]], resize_keyboard=True)

# Row headers to skip when bulk-importing student names from a file.
NAME_HEADER_WORDS = {"name", "student", "student name", "full name", "students"}

# In-memory roll-call sessions while a teacher is actively marking attendance.
# key: short token -> {"section_id", "section_path", "date", "teacher_id",
#                       "students": [(id, name), ...], "statuses": {student_id: status}}
pending_attendance = {}

# In-memory bulk-upload requests: admin telegram_id -> {"section_id", "path"}
# Set by /addstudents, consumed by the next document the admin sends.
pending_bulk_upload = {}


# --- Health-check HTTP server (for free-tier "Web Service" hosting) ---
# The bot itself only needs Telegram long-polling, but free hosting tiers
# that only offer "Web Service" plans require something listening on $PORT
# and passing a health check. This satisfies that while the real bot logic
# runs via polling in the same process.

class PingHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-type", "text/plain")
        self.end_headers()
        self.wfile.write(b"OK - school attendance bot is running")

    def log_message(self, format, *args):
        pass


def start_ping_server():
    port = int(os.environ.get("PORT", 10000))
    server = HTTPServer(("0.0.0.0", port), PingHandler)
    print(f"[keep-alive] HTTP ping server on port {port}")
    server.serve_forever()


# --- Database (SQLite locally, Postgres in production via DATABASE_URL) ---
#
# A thin wrapper so the rest of the code can use one sqlite3-style API
# (conn.execute(sql, params).fetchone()/.fetchall(), row["column"] access)
# regardless of which backend is active. SQL below is written with "?"
# placeholders throughout; the wrapper converts them to "%s" automatically
# when running against Postgres.

class _PGConnWrapper:
    """Makes a psycopg2 connection support conn.execute(...) like sqlite3 does."""
    def __init__(self, conn):
        self._conn = conn

    def execute(self, sql, params=()):
        sql = sql.replace("?", "%s")
        cur = self._conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute(sql, params)
        return cur

    def commit(self):
        self._conn.commit()

    def close(self):
        self._conn.close()


def db():
    if USE_POSTGRES:
        raw = psycopg2.connect(DATABASE_URL)
        return _PGConnWrapper(raw)
    else:
        conn = sqlite3.connect(DB_PATH)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA foreign_keys = ON")
        return conn


def init_db():
    conn = db()
    if USE_POSTGRES:
        id_type = "SERIAL PRIMARY KEY"
    else:
        id_type = "INTEGER PRIMARY KEY AUTOINCREMENT"

    conn.execute("""
        CREATE TABLE IF NOT EXISTS admins (
            telegram_id BIGINT PRIMARY KEY
        )
    """)
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS buildings (
            id {id_type},
            name TEXT UNIQUE
        )
    """)
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS grades (
            id {id_type},
            name TEXT,
            building_id INTEGER REFERENCES buildings(id),
            UNIQUE(name, building_id)
        )
    """)
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS sections (
            id {id_type},
            name TEXT,
            grade_id INTEGER REFERENCES grades(id),
            UNIQUE(name, grade_id)
        )
    """)
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS students (
            id {id_type},
            name TEXT,
            section_id INTEGER REFERENCES sections(id),
            link_code TEXT UNIQUE,
            parent_chat_id BIGINT
        )
    """)
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS teachers (
            id {id_type},
            telegram_id BIGINT UNIQUE,
            name TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS teacher_sections (
            teacher_id INTEGER REFERENCES teachers(id),
            section_id INTEGER REFERENCES sections(id),
            UNIQUE(teacher_id, section_id)
        )
    """)
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS attendance (
            id {id_type},
            student_id INTEGER REFERENCES students(id),
            date TEXT,
            status TEXT,
            marked_by BIGINT,
            marked_at TEXT,
            UNIQUE(student_id, date)
        )
    """)
    conn.commit()
    conn.close()
    print(f"[db] Using {'Postgres' if USE_POSTGRES else 'SQLite (' + DB_PATH + ')'}")


def is_admin(telegram_id: int) -> bool:
    conn = db()
    row = conn.execute("SELECT 1 FROM admins WHERE telegram_id = ?", (telegram_id,)).fetchone()
    conn.close()
    return row is not None


def any_admin_exists() -> bool:
    conn = db()
    row = conn.execute("SELECT 1 FROM admins LIMIT 1").fetchone()
    conn.close()
    return row is not None


def is_teacher(telegram_id: int) -> bool:
    conn = db()
    row = conn.execute("SELECT 1 FROM teachers WHERE telegram_id = ?", (telegram_id,)).fetchone()
    conn.close()
    return row is not None


# --- Class path helpers ("Building > Grade > Section") ---
# Name matching is done via LOWER(...) = LOWER(?) rather than relying on a
# case-insensitive collation, so the exact same SQL works on both SQLite
# and Postgres without any dialect-specific setup.

def parse_path(path_str: str):
    parts = [p.strip() for p in path_str.split(">")]
    if len(parts) != 3 or not all(parts):
        return None
    return tuple(parts)  # (building, grade, section)


def get_or_create_class_path(path_str: str):
    """Used by /addclass -- creates any missing levels."""
    parsed = parse_path(path_str)
    if not parsed:
        return None, "Format must be: Building > Grade > Section"
    building_name, grade_name, section_name = parsed

    conn = db()
    b = conn.execute("SELECT id FROM buildings WHERE LOWER(name) = LOWER(?)", (building_name,)).fetchone()
    if not b:
        conn.execute("INSERT INTO buildings (name) VALUES (?)", (building_name,))
        conn.commit()
        b = conn.execute("SELECT id FROM buildings WHERE LOWER(name) = LOWER(?)", (building_name,)).fetchone()

    g = conn.execute(
        "SELECT id FROM grades WHERE LOWER(name) = LOWER(?) AND building_id = ?", (grade_name, b["id"])
    ).fetchone()
    if not g:
        conn.execute("INSERT INTO grades (name, building_id) VALUES (?, ?)", (grade_name, b["id"]))
        conn.commit()
        g = conn.execute(
            "SELECT id FROM grades WHERE LOWER(name) = LOWER(?) AND building_id = ?", (grade_name, b["id"])
        ).fetchone()

    s = conn.execute(
        "SELECT id FROM sections WHERE LOWER(name) = LOWER(?) AND grade_id = ?", (section_name, g["id"])
    ).fetchone()
    if not s:
        conn.execute("INSERT INTO sections (name, grade_id) VALUES (?, ?)", (section_name, g["id"]))
        conn.commit()
        s = conn.execute(
            "SELECT id FROM sections WHERE LOWER(name) = LOWER(?) AND grade_id = ?", (section_name, g["id"])
        ).fetchone()

    conn.close()
    return {"section_id": s["id"], "path": f"{building_name} > {grade_name} > {section_name}"}, None


def find_class_path(path_str: str):
    """Used everywhere else -- the class must already exist."""
    parsed = parse_path(path_str)
    if not parsed:
        return None, "Format must be: Building > Grade > Section"
    building_name, grade_name, section_name = parsed

    conn = db()
    row = conn.execute("""
        SELECT sections.id AS section_id
        FROM sections
        JOIN grades ON sections.grade_id = grades.id
        JOIN buildings ON grades.building_id = buildings.id
        WHERE LOWER(buildings.name) = LOWER(?) AND LOWER(grades.name) = LOWER(?) AND LOWER(sections.name) = LOWER(?)
    """, (building_name, grade_name, section_name)).fetchone()
    conn.close()

    if not row:
        return None, f"No class found matching '{path_str}'. Check spelling or use /addclass first."
    return {"section_id": row["section_id"], "path": path_str}, None


def get_section_path(section_id: int):
    """Look up the full 'Building > Grade > Section' string from a section id."""
    conn = db()
    row = conn.execute("""
        SELECT buildings.name AS building_name, grades.name AS grade_name, sections.name AS section_name
        FROM sections
        JOIN grades ON sections.grade_id = grades.id
        JOIN buildings ON grades.building_id = buildings.id
        WHERE sections.id = ?
    """, (section_id,)).fetchone()
    conn.close()
    if not row:
        return None
    return f"{row['building_name']} > {row['grade_name']} > {row['section_name']}"


def class_tree_text() -> str:
    conn = db()
    buildings = conn.execute("SELECT * FROM buildings ORDER BY name").fetchall()
    lines = []
    for b in buildings:
        lines.append(f"🏫 {b['name']}")
        grades = conn.execute(
            "SELECT * FROM grades WHERE building_id = ? ORDER BY name", (b["id"],)
        ).fetchall()
        for g in grades:
            lines.append(f"  📚 {g['name']}")
            sections = conn.execute(
                "SELECT * FROM sections WHERE grade_id = ? ORDER BY name", (g["id"],)
            ).fetchall()
            for s in sections:
                count = conn.execute(
                    "SELECT COUNT(*) AS c FROM students WHERE section_id = ?", (s["id"],)
                ).fetchone()["c"]
                lines.append(f"    🧑‍🤝‍🧑 {s['name']} ({count} students)")
    conn.close()
    return "\n".join(lines) if lines else "No classes set up yet. Use /addclass to start."


# --- Handlers: admin bootstrap & setup ---

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    args = context.args

    # Deep-link parent linking: t.me/<bot>?start=<code>
    if args:
        await try_link_parent(update, args[0])
        return

    if not any_admin_exists():
        conn = db()
        conn.execute("INSERT INTO admins (telegram_id) VALUES (?)", (telegram_id,))
        conn.commit()
        conn.close()
        await update.message.reply_text(
            "👋 Welcome! No admin existed yet, so you're now the first admin.\n\n"
            "Use /addclass to start building your school's structure. Send /help for a full command list."
        )
        return

    if is_admin(telegram_id):
        await update.message.reply_text("Welcome back, admin. Send /help for commands.")
        return

    if is_teacher(telegram_id):
        await update.message.reply_text(
            "👋 Welcome back! Tap the button below to see your classes and take attendance.",
            reply_markup=TEACHER_MENU,
        )
        return

    await update.message.reply_text(
        "👋 Welcome! If you're a parent, use /link <code> with the code the school gave you.\n"
        "If you're a teacher, ask an admin to add you with /addteacher."
    )


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    lines = ["/myclasses - see your assigned classes as buttons (teachers)",
             "/attendance <Building > Grade > Section> - take attendance by typing the class",
             "/link <code> - parents: link yourself to your child"]
    if is_admin(telegram_id):
        lines = [
            "/addadmin <telegram_id>",
            "/addclass <Building > Grade > Section>",
            "/addstudent <Building > Grade > Section> | <Student Name>",
            "/addstudents <Building > Grade > Section> - then upload an Excel/CSV/PDF list",
            "/addteacher <numeric id> <Teacher Name>",
            "/assignteacher <numeric id> <Building > Grade > Section>",
            "/listclasses",
            "/liststudents <Building > Grade > Section>",
            "/studentcode <Building > Grade > Section> | <Student Name>",
            "/absentees [YYYY-MM-DD]",
        ] + lines
    await update.message.reply_text("\n".join(lines))


def require_admin(func):
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            await update.message.reply_text("This command is admin-only.")
            return
        await func(update, context)
    return wrapper


@require_admin
async def cmd_addadmin(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args or not context.args[0].isdigit():
        await update.message.reply_text("Usage: /addadmin <telegram_id>")
        return
    new_id = int(context.args[0])
    conn = db()
    conn.execute("INSERT INTO admins (telegram_id) VALUES (?) ON CONFLICT (telegram_id) DO NOTHING", (new_id,))
    conn.commit()
    conn.close()
    await update.message.reply_text(f"✅ {new_id} is now an admin.")


@require_admin
async def cmd_addclass(update: Update, context: ContextTypes.DEFAULT_TYPE):
    path_str = " ".join(context.args)
    result, error = get_or_create_class_path(path_str)
    if error:
        await update.message.reply_text(f"❌ {error}")
        return
    await update.message.reply_text(f"✅ Class ready: {result['path']}")


@require_admin
async def cmd_addstudent(update: Update, context: ContextTypes.DEFAULT_TYPE):
    full = " ".join(context.args)
    if "|" not in full:
        await update.message.reply_text(
            "Usage: /addstudent Building > Grade > Section | Student Full Name"
        )
        return
    path_str, student_name = (p.strip() for p in full.split("|", 1))
    if not student_name:
        await update.message.reply_text("Please include the student's name after '|'.")
        return

    result, error = find_class_path(path_str)
    if error:
        await update.message.reply_text(f"❌ {error}")
        return

    link_code = secrets.token_hex(3).upper()  # e.g. "A1B2C3"
    conn = db()
    conn.execute(
        "INSERT INTO students (name, section_id, link_code) VALUES (?, ?, ?)",
        (student_name, result["section_id"], link_code),
    )
    conn.commit()
    conn.close()

    await update.message.reply_text(
        f"✅ Added {student_name} to {result['path']}.\n\n"
        f"Parent link code: `{link_code}`\n"
        f"Give this to the parent — they send /link {link_code} to this bot to get absence notifications.",
        parse_mode="Markdown",
    )


@require_admin
async def cmd_addstudents(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Bulk-add: sets up a pending upload, then on_document does the actual import."""
    path_str = " ".join(context.args)
    if not path_str:
        await update.message.reply_text(
            "Usage: /addstudents Building > Grade > Section\n"
            "Then upload an Excel (.xlsx), CSV (.csv), or PDF (.pdf) file with one "
            "student name per row/line."
        )
        return

    result, error = find_class_path(path_str)
    if error:
        await update.message.reply_text(f"❌ {error}")
        return

    pending_bulk_upload[update.effective_user.id] = result
    await update.message.reply_text(
        f"📎 Ready. Now upload an Excel (.xlsx), CSV (.csv), or PDF (.pdf) file with one "
        f"student name per row/line — I'll add them all to {result['path']}."
    )


def _extract_names_from_xlsx(file_bytes: bytes):
    import openpyxl
    wb = openpyxl.load_workbook(io.BytesIO(file_bytes), data_only=True)
    ws = wb.active
    names = []
    for row in ws.iter_rows(values_only=True):
        if not row:
            continue
        cell = row[0]
        if cell is None:
            continue
        name = str(cell).strip()
        if name and name.lower() not in NAME_HEADER_WORDS:
            names.append(name)
    return names


def _extract_names_from_csv(file_bytes: bytes):
    text = file_bytes.decode("utf-8", errors="ignore")
    reader = csv.reader(io.StringIO(text))
    names = []
    for row in reader:
        if not row:
            continue
        name = row[0].strip()
        if name and name.lower() not in NAME_HEADER_WORDS:
            names.append(name)
    return names


def _extract_names_from_pdf(file_bytes: bytes):
    import pdfplumber
    names = []
    with pdfplumber.open(io.BytesIO(file_bytes)) as pdf:
        for page in pdf.pages:
            text = page.extract_text() or ""
            for line in text.split("\n"):
                line = line.strip()
                if line and line.lower() not in NAME_HEADER_WORDS:
                    names.append(line)
    return names


async def on_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    pending = pending_bulk_upload.get(telegram_id)
    if not pending:
        # Not expecting a file from this user right now -- ignore silently.
        return

    document = update.message.document
    filename = document.file_name or ""
    ext = filename.lower().rsplit(".", 1)[-1] if "." in filename else ""

    if ext not in ("xlsx", "csv", "pdf"):
        await update.message.reply_text("❌ Unsupported file type. Please send a .xlsx, .csv, or .pdf file.")
        return

    tg_file = await document.get_file()
    file_bytes = bytes(await tg_file.download_as_bytearray())

    try:
        if ext == "xlsx":
            names = _extract_names_from_xlsx(file_bytes)
        elif ext == "csv":
            names = _extract_names_from_csv(file_bytes)
        else:
            names = _extract_names_from_pdf(file_bytes)
    except Exception as e:
        await update.message.reply_text(f"❌ Couldn't read that file: {e}")
        return

    if not names:
        await update.message.reply_text(
            "❌ No student names found in that file. Make sure each name is in its own "
            "row (Excel/CSV) or its own line (PDF)."
        )
        return

    conn = db()
    added = []
    for name in names:
        link_code = secrets.token_hex(3).upper()
        conn.execute(
            "INSERT INTO students (name, section_id, link_code) VALUES (?, ?, ?)",
            (name, pending["section_id"], link_code),
        )
        added.append((name, link_code))
    conn.commit()
    conn.close()

    pending_bulk_upload.pop(telegram_id, None)

    header = f"✅ Added {len(added)} students to {pending['path']}:\n"
    body_lines = [f"  • {name} — `{code}`" for name, code in added]

    # Telegram caps messages at ~4096 chars -- chunk the codes list if long.
    chunk = header
    for line in body_lines:
        if len(chunk) + len(line) + 1 > 3500:
            await update.message.reply_text(chunk, parse_mode="Markdown")
            chunk = ""
        chunk += line + "\n"
    if chunk:
        await update.message.reply_text(chunk, parse_mode="Markdown")


@require_admin
async def cmd_addteacher(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if len(context.args) < 2:
        await update.message.reply_text("Usage: /addteacher <telegram_id> <Teacher Name>")
        return
    identifier = context.args[0]
    teacher_name = " ".join(context.args[1:])

    if not identifier.lstrip("@").isdigit():
        await update.message.reply_text(
            "Please use the teacher's numeric Telegram ID (ask them to message "
            "@userinfobot to find it), not just their @username."
        )
        return
    telegram_id = int(identifier.lstrip("@"))

    conn = db()
    conn.execute(
        "INSERT INTO teachers (telegram_id, name) VALUES (?, ?) ON CONFLICT (telegram_id) DO NOTHING",
        (telegram_id, teacher_name),
    )
    conn.commit()
    conn.close()
    await update.message.reply_text(f"✅ Teacher added: {teacher_name} ({telegram_id})")


@require_admin
async def cmd_assignteacher(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.message.reply_text(
            "Usage: /assignteacher <telegram_id> <Building > Grade > Section>"
        )
        return
    identifier = context.args[0]
    path_str = " ".join(context.args[1:])

    if not identifier.lstrip("@").isdigit():
        await update.message.reply_text("Please use the teacher's numeric Telegram ID.")
        return
    telegram_id = int(identifier.lstrip("@"))

    result, error = find_class_path(path_str)
    if error:
        await update.message.reply_text(f"❌ {error}")
        return

    conn = db()
    teacher = conn.execute("SELECT id, name FROM teachers WHERE telegram_id = ?", (telegram_id,)).fetchone()
    if not teacher:
        await update.message.reply_text("That teacher isn't registered yet — use /addteacher first.")
        conn.close()
        return

    conn.execute(
        "INSERT INTO teacher_sections (teacher_id, section_id) VALUES (?, ?) "
        "ON CONFLICT (teacher_id, section_id) DO NOTHING",
        (teacher["id"], result["section_id"]),
    )
    conn.commit()
    conn.close()
    await update.message.reply_text(f"✅ {teacher['name']} assigned to {result['path']}")


@require_admin
async def cmd_listclasses(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(class_tree_text())


@require_admin
async def cmd_liststudents(update: Update, context: ContextTypes.DEFAULT_TYPE):
    path_str = " ".join(context.args)
    result, error = find_class_path(path_str)
    if error:
        await update.message.reply_text(f"❌ {error}")
        return

    conn = db()
    students = conn.execute(
        "SELECT name, parent_chat_id FROM students WHERE section_id = ? ORDER BY name",
        (result["section_id"],),
    ).fetchall()
    conn.close()

    if not students:
        await update.message.reply_text(f"No students in {result['path']} yet.")
        return

    lines = [f"🧑‍🤝‍🧑 {result['path']}:"]
    for s in students:
        linked = "🔗 linked" if s["parent_chat_id"] else "⚠️ not linked"
        lines.append(f"  • {s['name']} — {linked}")
    await update.message.reply_text("\n".join(lines))


@require_admin
async def cmd_studentcode(update: Update, context: ContextTypes.DEFAULT_TYPE):
    full = " ".join(context.args)
    if "|" not in full:
        await update.message.reply_text("Usage: /studentcode Building > Grade > Section | Student Name")
        return
    path_str, student_name = (p.strip() for p in full.split("|", 1))
    result, error = find_class_path(path_str)
    if error:
        await update.message.reply_text(f"❌ {error}")
        return

    conn = db()
    student = conn.execute(
        "SELECT name, link_code, parent_chat_id FROM students WHERE section_id = ? AND LOWER(name) LIKE LOWER(?)",
        (result["section_id"], f"%{student_name}%"),
    ).fetchone()
    conn.close()

    if not student:
        await update.message.reply_text(f"No student matching '{student_name}' found in {result['path']}.")
        return

    linked = "already linked to a parent" if student["parent_chat_id"] else "not yet linked"
    await update.message.reply_text(
        f"{student['name']}: code `{student['link_code']}` ({linked})", parse_mode="Markdown"
    )


@require_admin
async def cmd_absentees(update: Update, context: ContextTypes.DEFAULT_TYPE):
    target_date = context.args[0] if context.args else date.today().isoformat()
    conn = db()
    rows = conn.execute("""
        SELECT students.name AS student_name, attendance.status,
               sections.name AS section_name, grades.name AS grade_name, buildings.name AS building_name
        FROM attendance
        JOIN students ON attendance.student_id = students.id
        JOIN sections ON students.section_id = sections.id
        JOIN grades ON sections.grade_id = grades.id
        JOIN buildings ON grades.building_id = buildings.id
        WHERE attendance.date = ? AND attendance.status IN ('absent', 'late')
        ORDER BY building_name, grade_name, section_name, student_name
    """, (target_date,)).fetchall()
    conn.close()

    if not rows:
        await update.message.reply_text(f"No absences/lates recorded for {target_date}.")
        return

    lines = [f"📋 Absentees/late for {target_date}:"]
    for r in rows:
        emoji = STATUS_EMOJI[r["status"]]
        lines.append(
            f"  {emoji} {r['student_name']} — {r['building_name']} > {r['grade_name']} > {r['section_name']}"
        )
    await update.message.reply_text("\n".join(lines))


# --- Teacher handlers ---

def build_myclasses_keyboard(rows):
    """rows: list of dicts with building_name/grade_name/section_name/section_id."""
    buttons = []
    for r in rows:
        label = f"{r['building_name']} > {r['grade_name']} > {r['section_name']}"
        buttons.append([InlineKeyboardButton(label, callback_data=f"pickclass:{r['section_id']}")])
    return InlineKeyboardMarkup(buttons)


async def cmd_myclasses(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    conn = db()
    teacher = conn.execute("SELECT id FROM teachers WHERE telegram_id = ?", (telegram_id,)).fetchone()
    if not teacher:
        await update.message.reply_text("You're not registered as a teacher. Ask an admin to add you.")
        conn.close()
        return

    rows = conn.execute("""
        SELECT sections.id AS section_id,
               buildings.name AS building_name, grades.name AS grade_name, sections.name AS section_name
        FROM teacher_sections
        JOIN sections ON teacher_sections.section_id = sections.id
        JOIN grades ON sections.grade_id = grades.id
        JOIN buildings ON grades.building_id = buildings.id
        WHERE teacher_sections.teacher_id = ?
        ORDER BY building_name, grade_name, section_name
    """, (teacher["id"],)).fetchall()
    conn.close()

    if not rows:
        await update.message.reply_text("You're not assigned to any classes yet. Ask an admin to /assignteacher you.")
        return

    await update.message.reply_text(
        "Tap a class to start attendance:",
        reply_markup=build_myclasses_keyboard(rows),
    )


async def on_myclasses_button_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the persistent '📋 My Classes' reply-keyboard button."""
    await cmd_myclasses(update, context)


def build_attendance_keyboard(token: str):
    session = pending_attendance[token]
    rows = []
    for student_id, student_name in session["students"]:
        status = session["statuses"][student_id]
        emoji = STATUS_EMOJI[status]
        rows.append([InlineKeyboardButton(f"{emoji} {student_name}", callback_data=f"att:{token}:{student_id}")])
    rows.append([InlineKeyboardButton("✅ Submit Attendance", callback_data=f"attsubmit:{token}")])
    return InlineKeyboardMarkup(rows)


def _start_attendance_session(section_id: int, section_path: str, teacher_id: int):
    """Shared by /attendance and the 'pick a class' button. Returns (token, error)."""
    conn = db()
    students = conn.execute(
        "SELECT id, name FROM students WHERE section_id = ? ORDER BY name",
        (section_id,),
    ).fetchall()
    conn.close()

    if not students:
        return None, f"No students in {section_path} yet."

    token = secrets.token_hex(4)
    pending_attendance[token] = {
        "section_id": section_id,
        "section_path": section_path,
        "date": date.today().isoformat(),
        "teacher_id": teacher_id,
        "students": [(s["id"], s["name"]) for s in students],
        "statuses": {s["id"]: "present" for s in students},
    }
    return token, None


async def cmd_attendance(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    path_str = " ".join(context.args)

    result, error = find_class_path(path_str)
    if error:
        await update.message.reply_text(f"❌ {error}")
        return

    conn = db()
    teacher = conn.execute("SELECT id FROM teachers WHERE telegram_id = ?", (telegram_id,)).fetchone()
    is_this_admin = is_admin(telegram_id)

    if not teacher and not is_this_admin:
        await update.message.reply_text("You're not registered as a teacher.")
        conn.close()
        return

    if teacher and not is_this_admin:
        assigned = conn.execute(
            "SELECT 1 FROM teacher_sections WHERE teacher_id = ? AND section_id = ?",
            (teacher["id"], result["section_id"]),
        ).fetchone()
        if not assigned:
            await update.message.reply_text("You're not assigned to this class.")
            conn.close()
            return
    conn.close()

    token, error = _start_attendance_session(result["section_id"], result["path"], telegram_id)
    if error:
        await update.message.reply_text(error)
        return

    await update.message.reply_text(
        f"📋 Attendance for {result['path']} — {date.today().isoformat()}\n"
        f"Tap a name to cycle Present → Absent → Late. Everyone starts as Present.",
        reply_markup=build_attendance_keyboard(token),
    )


async def on_pickclass(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles tapping a class button from /myclasses -- starts attendance directly."""
    query = update.callback_query
    telegram_id = update.effective_user.id
    section_id = int(query.data.split(":")[1])

    section_path = get_section_path(section_id)
    if not section_path:
        await query.answer("That class no longer exists.", show_alert=True)
        return

    conn = db()
    teacher = conn.execute("SELECT id FROM teachers WHERE telegram_id = ?", (telegram_id,)).fetchone()
    is_this_admin = is_admin(telegram_id)

    if not teacher and not is_this_admin:
        conn.close()
        await query.answer("You're not registered as a teacher.", show_alert=True)
        return

    if teacher and not is_this_admin:
        assigned = conn.execute(
            "SELECT 1 FROM teacher_sections WHERE teacher_id = ? AND section_id = ?",
            (teacher["id"], section_id),
        ).fetchone()
        if not assigned:
            conn.close()
            await query.answer("You're not assigned to this class.", show_alert=True)
            return
    conn.close()

    token, error = _start_attendance_session(section_id, section_path, telegram_id)
    if error:
        await query.answer()
        await query.message.reply_text(error)
        return

    await query.answer()
    await query.message.reply_text(
        f"📋 Attendance for {section_path} — {date.today().isoformat()}\n"
        f"Tap a name to cycle Present → Absent → Late. Everyone starts as Present.",
        reply_markup=build_attendance_keyboard(token),
    )


async def on_attendance_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data

    if data.startswith("att:"):
        _, token, student_id_str = data.split(":")
        student_id = int(student_id_str)
        session = pending_attendance.get(token)
        if not session:
            await query.answer("This attendance session expired.", show_alert=True)
            return
        current = session["statuses"][student_id]
        next_status = STATUS_CYCLE[(STATUS_CYCLE.index(current) + 1) % len(STATUS_CYCLE)]
        session["statuses"][student_id] = next_status
        await query.answer()
        await query.edit_message_reply_markup(reply_markup=build_attendance_keyboard(token))
        return

    if data.startswith("attsubmit:"):
        _, token = data.split(":")
        session = pending_attendance.pop(token, None)
        if not session:
            await query.answer("This attendance session already expired.", show_alert=True)
            return
        await query.answer("Submitting...")
        await submit_attendance(context, session)
        summary = "\n".join(
            f"{STATUS_EMOJI[session['statuses'][sid]]} {name}" for sid, name in session["students"]
        )
        await query.edit_message_text(
            f"✅ Attendance submitted for {session['section_path']} — {session['date']}\n\n{summary}"
        )
        return


async def submit_attendance(context: ContextTypes.DEFAULT_TYPE, session: dict):
    conn = db()
    for student_id, status in session["statuses"].items():
        conn.execute("""
            INSERT INTO attendance (student_id, date, status, marked_by, marked_at)
            VALUES (?, ?, ?, ?, ?)
            ON CONFLICT(student_id, date) DO UPDATE SET status=excluded.status, marked_at=excluded.marked_at
        """, (student_id, session["date"], status, session["teacher_id"], datetime.now().isoformat(timespec="seconds")))
    conn.commit()

    # Notify parents of absent/late students
    for student_id, status in session["statuses"].items():
        if status == "present":
            continue
        row = conn.execute(
            "SELECT name, parent_chat_id FROM students WHERE id = ?", (student_id,)
        ).fetchone()
        if row and row["parent_chat_id"]:
            emoji = STATUS_EMOJI[status]
            try:
                await context.bot.send_message(
                    chat_id=row["parent_chat_id"],
                    text=f"{emoji} {row['name']} was marked {status.upper()} today "
                         f"in {session['section_path']} ({session['date']}).",
                )
            except Exception as e:
                print(f"[notify] Failed to notify parent of student {student_id}: {e}")
    conn.close()


# --- Parent linking ---

async def try_link_parent(update: Update, code: str):
    code = code.strip().upper()
    chat_id = update.effective_chat.id

    conn = db()
    student = conn.execute("SELECT id, name, parent_chat_id FROM students WHERE link_code = ?", (code,)).fetchone()
    if not student:
        await update.message.reply_text("❌ That code isn't valid. Please double-check it with the school.")
        conn.close()
        return

    if student["parent_chat_id"]:
        await update.message.reply_text(f"This code is already linked to a parent account for {student['name']}.")
        conn.close()
        return

    conn.execute("UPDATE students SET parent_chat_id = ? WHERE id = ?", (chat_id, student["id"]))
    conn.commit()
    conn.close()

    await update.message.reply_text(
        f"✅ Linked! You'll now be notified here if {student['name']} is marked absent or late."
    )


async def cmd_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.message.reply_text("Usage: /link <code>")
        return
    await try_link_parent(update, context.args[0])


# --- Main ---

def main():
    init_db()
    threading.Thread(target=start_ping_server, daemon=True).start()

    app = Application.builder().token(BOT_TOKEN).build()

    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("help", cmd_help))
    app.add_handler(CommandHandler("addadmin", cmd_addadmin))
    app.add_handler(CommandHandler("addclass", cmd_addclass))
    app.add_handler(CommandHandler("addstudent", cmd_addstudent))
    app.add_handler(CommandHandler("addstudents", cmd_addstudents))
    app.add_handler(CommandHandler("addteacher", cmd_addteacher))
    app.add_handler(CommandHandler("assignteacher", cmd_assignteacher))
    app.add_handler(CommandHandler("listclasses", cmd_listclasses))
    app.add_handler(CommandHandler("liststudents", cmd_liststudents))
    app.add_handler(CommandHandler("studentcode", cmd_studentcode))
    app.add_handler(CommandHandler("absentees", cmd_absentees))
    app.add_handler(CommandHandler("myclasses", cmd_myclasses))
    app.add_handler(CommandHandler("attendance", cmd_attendance))
    app.add_handler(CommandHandler("link", cmd_link))
    app.add_handler(CallbackQueryHandler(on_attendance_button, pattern="^(att|attsubmit):"))
    app.add_handler(CallbackQueryHandler(on_pickclass, pattern="^pickclass:"))
    app.add_handler(MessageHandler(filters.Regex(f"^{MY_CLASSES_LABEL}$"), on_myclasses_button_text))
    app.add_handler(MessageHandler(filters.Document.ALL, on_document))

    print("School attendance bot running.")
    app.run_polling()


if __name__ == "__main__":
    main()
