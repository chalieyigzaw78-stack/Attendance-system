"""
School Attendance Bot (python-telegram-bot)
-----------------------------------------------
A Telegram bot for schools: teachers take attendance from their phone,
parents get notified instantly if their child is marked absent/late, and
the whole school structure (buildings, grades, sections, students,
teachers) is built up THROUGH the bot -- nothing needs to be known or
configured in advance.

Both ADMINS and TEACHERS get a button menu after /start (or /menu) so
almost nothing needs to be typed by hand -- the bot asks for whatever it
needs, one step at a time, and lets you pick existing classes/teachers/
students from a list instead of typing their names. The original slash
commands still work too, for anyone who prefers typing.

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

ADMIN -- BUTTON MENU (shown automatically after /start, or via /menu):
  ➕ Add Class            -- walks you through Building / Grade / Section
  📦 Bulk Add Classes     -- e.g. Waliya > Grade 6 > Section A to H creates
                             Section A, B, C ... H in one go
  ✏️ Edit Class           -- pick a class, rename its building/grade/section
  🧑‍🎓 Add Student          -- pick a class, then send the student's name
  📥 Bulk Add Students    -- pick a class, then upload an Excel/CSV/PDF
  ✏️ Edit Student         -- pick a class + student, then Rename or
                             Move to Another Class
  👨‍🏫 Add Teacher          -- send their numeric Telegram ID + name
  🔗 Assign Teacher       -- pick a teacher, then pick a class
  📚 List Classes         -- shows the whole building/grade/section tree
  🧑‍🤝‍🧑 List Students        -- pick a class, see students + guardian counts
  🔑 Student Code         -- pick a class, then a student, see their code
  📋 Absentees Today      -- today's absent/late list
  ➕ Add Admin            -- send a numeric Telegram ID
  ❌ Cancel               -- cancels whatever you're in the middle of

ADMIN -- SLASH COMMANDS (still work, for typing instead of tapping):
  /addadmin <telegram_id>
  /addclass <Building > Grade > Section>
  /addclasses <Building > Grade > Section A to H>   (bulk letter range)
  /editclass <Old Path> | <New Path>
  /addstudent <Building > Grade > Section> | <Student Full Name>
  /addstudents <Building > Grade > Section>   (then upload a file)
  /editstudent <Building > Grade > Section> | <Old Name> | <New Name>
  /movestudent <Old Path> | <Student Name> | <New Path>
  /addteacher <numeric telegram id> <Teacher Name>
  /assignteacher <numeric telegram id> <Building > Grade > Section>
  /listclasses
  /liststudents <Building > Grade > Section>
  /studentcode <Building > Grade > Section> | <Student Name>
  /absentees [YYYY-MM-DD]

TEACHER:
  A persistent "📋 My Classes" button appears after /start. Tapping it
  shows the teacher's classes as buttons; tapping a class starts
  attendance immediately. /myclasses and /attendance <class path> still
  work too.

PARENT / GUARDIAN:
  /link <code>
      Links this Telegram chat to a student using the code the school
      gave you. Multiple people (mother, father, another guardian) can
      each send /link with the SAME code -- every linked chat gets
      notified whenever that student is marked absent or late.

  You can also just tap a t.me/<bot>?start=<code> link if the school
  shares one directly.
"""

import os
import io
import re
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

# Row headers to skip when bulk-importing student names from a file.
NAME_HEADER_WORDS = {"name", "student", "student name", "full name", "students"}

# --- Reply-keyboard button labels ---
MY_CLASSES_LABEL = "📋 My Classes"
TEACHER_MENU = ReplyKeyboardMarkup([[MY_CLASSES_LABEL]], resize_keyboard=True)

BTN_ADD_CLASS = "➕ Add Class"
BTN_BULK_CLASSES = "📦 Bulk Add Classes"
BTN_EDIT_CLASS = "✏️ Edit Class"
BTN_ADD_STUDENT = "🧑‍🎓 Add Student"
BTN_BULK_STUDENTS = "📥 Bulk Add Students"
BTN_EDIT_STUDENT = "✏️ Edit Student"
BTN_ADD_TEACHER = "👨‍🏫 Add Teacher"
BTN_ASSIGN_TEACHER = "🔗 Assign Teacher"
BTN_LIST_CLASSES = "📚 List Classes"
BTN_LIST_STUDENTS = "🧑‍🤝‍🧑 List Students"
BTN_STUDENT_CODE = "🔑 Student Code"
BTN_ABSENTEES = "📋 Absentees Today"
BTN_ADD_ADMIN = "➕ Add Admin"
BTN_CANCEL = "❌ Cancel"

ADMIN_MENU = ReplyKeyboardMarkup(
    [
        [BTN_ADD_CLASS, BTN_BULK_CLASSES],
        [BTN_EDIT_CLASS, BTN_ADD_STUDENT],
        [BTN_BULK_STUDENTS, BTN_EDIT_STUDENT],
        [BTN_ADD_TEACHER, BTN_ASSIGN_TEACHER],
        [BTN_LIST_CLASSES, BTN_LIST_STUDENTS],
        [BTN_STUDENT_CODE, BTN_ABSENTEES],
        [BTN_ADD_ADMIN],
        [BTN_CANCEL],
    ],
    resize_keyboard=True,
)
FLOW_CANCEL_MENU = ReplyKeyboardMarkup([[BTN_CANCEL]], resize_keyboard=True)

# In-memory roll-call sessions while a teacher is actively marking attendance.
# key: short token -> {"section_id", "section_path", "date", "teacher_id",
#                       "students": [(id, name), ...], "statuses": {student_id: status}}
pending_attendance = {}

# In-memory bulk-upload requests: admin telegram_id -> {"section_id", "path"}
# Set by /addstudents or the 📥 Bulk Add Students button, consumed by the
# next document the admin sends.
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
    # Multiple guardians per student (mother, father, another guardian, etc).
    # Everyone linked here gets notified on absence/late -- not just one.
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS parent_links (
            id {id_type},
            student_id INTEGER REFERENCES students(id),
            chat_id BIGINT,
            UNIQUE(student_id, chat_id)
        )
    """)
    conn.commit()

    # One-time migration: carry forward any old single parent_chat_id
    # values (from before multi-guardian support) into parent_links.
    conn.execute("""
        INSERT INTO parent_links (student_id, chat_id)
        SELECT id, parent_chat_id FROM students
        WHERE parent_chat_id IS NOT NULL
        ON CONFLICT (student_id, chat_id) DO NOTHING
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


def parse_section_range(section_str: str):
    """Detect patterns like 'Section A to H' or 'Section A-H' and expand them
    into ['Section A', 'Section B', ..., 'Section H']. Returns None if the
    text isn't a letter range (caller should treat it as a single name)."""
    m = re.match(r'^(.*?)\s*([A-Za-z])\s*(?:to|-)\s*([A-Za-z])\s*$', section_str.strip(), re.IGNORECASE)
    if not m:
        return None
    prefix, start_letter, end_letter = m.groups()
    start_letter, end_letter = start_letter.upper(), end_letter.upper()
    start_ord, end_ord = ord(start_letter), ord(end_letter)
    if start_ord > end_ord or (end_ord - start_ord) > 25:
        return None
    prefix = prefix.strip()
    names = []
    for code in range(start_ord, end_ord + 1):
        letter = chr(code)
        names.append(f"{prefix} {letter}".strip() if prefix else letter)
    return names


def find_class_ids(path_str: str):
    """Like find_class_path, but returns the building/grade/section ids too
    (needed for renaming a level that's shared with other classes)."""
    parsed = parse_path(path_str)
    if not parsed:
        return None, "Format must be: Building > Grade > Section"
    building_name, grade_name, section_name = parsed
    conn = db()
    row = conn.execute("""
        SELECT buildings.id AS building_id, grades.id AS grade_id, sections.id AS section_id
        FROM sections
        JOIN grades ON sections.grade_id = grades.id
        JOIN buildings ON grades.building_id = buildings.id
        WHERE LOWER(buildings.name) = LOWER(?) AND LOWER(grades.name) = LOWER(?) AND LOWER(sections.name) = LOWER(?)
    """, (building_name, grade_name, section_name)).fetchone()
    conn.close()
    if not row:
        return None, f"No class found matching '{path_str}'."
    return {"building_id": row["building_id"], "grade_id": row["grade_id"], "section_id": row["section_id"]}, None


def get_class_ids_and_names(section_id: int):
    """Given a section id, return its building/grade ids and all three names
    -- used to seed the Edit Class wizard."""
    conn = db()
    row = conn.execute("""
        SELECT buildings.id AS building_id, buildings.name AS building_name,
               grades.id AS grade_id, grades.name AS grade_name,
               sections.name AS section_name
        FROM sections
        JOIN grades ON sections.grade_id = grades.id
        JOIN buildings ON grades.building_id = buildings.id
        WHERE sections.id = ?
    """, (section_id,)).fetchone()
    conn.close()
    return row


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


def get_all_sections():
    conn = db()
    rows = conn.execute("""
        SELECT sections.id AS section_id,
               buildings.name AS building_name, grades.name AS grade_name, sections.name AS section_name
        FROM sections
        JOIN grades ON sections.grade_id = grades.id
        JOIN buildings ON grades.building_id = buildings.id
        ORDER BY building_name, grade_name, section_name
    """).fetchall()
    conn.close()
    return rows


def get_all_teachers():
    conn = db()
    rows = conn.execute("SELECT id, telegram_id, name FROM teachers ORDER BY name").fetchall()
    conn.close()
    return rows


def get_students_in_section(section_id):
    conn = db()
    rows = conn.execute(
        "SELECT id, name FROM students WHERE section_id = ? ORDER BY name", (section_id,)
    ).fetchall()
    conn.close()
    return rows


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


def absentees_text(target_date: str) -> str:
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
        return f"No absences/lates recorded for {target_date}."

    lines = [f"📋 Absentees/late for {target_date}:"]
    for r in rows:
        emoji = STATUS_EMOJI[r["status"]]
        lines.append(
            f"  {emoji} {r['student_name']} — {r['building_name']} > {r['grade_name']} > {r['section_name']}"
        )
    return "\n".join(lines)


def notification_text(student_name: str, status: str, section_path: str, date_str: str) -> str:
    emoji = STATUS_EMOJI[status]
    if status == "absent":
        return (
            f"{emoji} {student_name} was marked ABSENT today in {section_path} ({date_str}).\n\n"
            f"Please call or check in with {student_name} to make sure everything is okay."
        )
    return (
        f"{emoji} {student_name} was marked LATE today in {section_path} ({date_str}).\n\n"
        f"Please check in with {student_name} — a reminder about arriving on time would help."
    )


# --- Inline keyboard builders (used by both admin buttons and flows) ---

def build_section_picker(sections, action):
    buttons = [
        [InlineKeyboardButton(
            f"{s['building_name']} > {s['grade_name']} > {s['section_name']}",
            callback_data=f"adm_sec:{action}:{s['section_id']}",
        )]
        for s in sections
    ]
    return InlineKeyboardMarkup(buttons)


def build_section_picker_with_extra(sections, action, extra):
    """Like build_section_picker, but packs an extra id (e.g. a student id)
    into the callback data -- used by the 'move student' flow."""
    buttons = [
        [InlineKeyboardButton(
            f"{s['building_name']} > {s['grade_name']} > {s['section_name']}",
            callback_data=f"adm_sec:{action}:{extra}:{s['section_id']}",
        )]
        for s in sections
    ]
    return InlineKeyboardMarkup(buttons)


def build_teacher_picker(teachers, action):
    buttons = [
        [InlineKeyboardButton(f"{t['name']} ({t['telegram_id']})", callback_data=f"adm_teacher:{action}:{t['id']}")]
        for t in teachers
    ]
    return InlineKeyboardMarkup(buttons)


def build_student_picker(students, action):
    buttons = [
        [InlineKeyboardButton(s["name"], callback_data=f"adm_student:{action}:{s['id']}")]
        for s in students
    ]
    return InlineKeyboardMarkup(buttons)


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
            "Use the buttons below to get started, or send /help for the full command list.",
            reply_markup=ADMIN_MENU,
        )
        return

    if is_admin(telegram_id):
        await update.message.reply_text(
            "Welcome back, admin. Use the buttons below, or /help for commands.",
            reply_markup=ADMIN_MENU,
        )
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


async def cmd_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    if is_admin(telegram_id):
        await update.message.reply_text("Admin menu:", reply_markup=ADMIN_MENU)
    elif is_teacher(telegram_id):
        await update.message.reply_text("Tap to see your classes:", reply_markup=TEACHER_MENU)
    else:
        await update.message.reply_text("Nothing to show here. Parents: use /link <code>.")


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    lines = ["/menu - show your button menu again",
             "/myclasses - see your assigned classes as buttons (teachers)",
             "/attendance <Building > Grade > Section> - take attendance by typing the class",
             "/link <code> - parents/guardians: link yourself to a child (works for more than one guardian per child)"]
    if is_admin(telegram_id):
        lines = [
            "/addadmin <telegram_id>",
            "/addclass <Building > Grade > Section>",
            "/addclasses <Building > Grade > Section A to H> - bulk-create lettered sections",
            "/editclass <Old Path> | <New Path> - rename a building/grade/section",
            "/addstudent <Building > Grade > Section> | <Student Name>",
            "/addstudents <Building > Grade > Section> - then upload an Excel/CSV/PDF list",
            "/editstudent <Building > Grade > Section> | <Old Name> | <New Name>",
            "/movestudent <Old Path> | <Student Name> | <New Path>",
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
async def cmd_addclasses(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Bulk-create classes from a letter range, e.g. Waliya > Grade 6 > Section A to H."""
    path_str = " ".join(context.args)
    parsed = parse_path(path_str)
    if not parsed:
        await update.message.reply_text(
            "Usage: /addclasses Building > Grade > Section A to H\n"
            "Example: /addclasses Waliya > Grade 6 > Section A to H"
        )
        return
    building, grade, section_spec = parsed
    section_names = parse_section_range(section_spec)
    if not section_names:
        await update.message.reply_text(
            "❌ Couldn't find a letter range like 'Section A to H' in that. "
            "For a single class, use /addclass instead."
        )
        return

    created = []
    for section_name in section_names:
        result, error = get_or_create_class_path(f"{building} > {grade} > {section_name}")
        if not error:
            created.append(result["path"])

    if not created:
        await update.message.reply_text("❌ Couldn't create any classes.")
        return
    lines = ["✅ Created:"] + [f"  • {p}" for p in created]
    await update.message.reply_text("\n".join(lines))


@require_admin
async def cmd_editclass(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Rename a class: /editclass Old Building > Old Grade > Old Section | New Building > New Grade > New Section"""
    full = " ".join(context.args)
    if "|" not in full:
        await update.message.reply_text(
            "Usage: /editclass Old Building > Old Grade > Old Section | New Building > New Grade > New Section"
        )
        return
    old_path, new_path = (p.strip() for p in full.split("|", 1))
    ids, error = find_class_ids(old_path)
    if error:
        await update.message.reply_text(f"❌ {error}")
        return
    new_parsed = parse_path(new_path)
    if not new_parsed:
        await update.message.reply_text("❌ New path format must be: Building > Grade > Section")
        return
    new_building, new_grade, new_section = new_parsed

    conn = db()
    try:
        conn.execute("UPDATE buildings SET name = ? WHERE id = ?", (new_building, ids["building_id"]))
        conn.execute("UPDATE grades SET name = ? WHERE id = ?", (new_grade, ids["grade_id"]))
        conn.execute("UPDATE sections SET name = ? WHERE id = ?", (new_section, ids["section_id"]))
        conn.commit()
    except Exception as e:
        conn.close()
        await update.message.reply_text(f"❌ Couldn't save changes: {e}")
        return
    conn.close()
    await update.message.reply_text(f"✅ Updated to: {new_building} > {new_grade} > {new_section}")


@require_admin
async def cmd_editstudent(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Rename a student: /editstudent Building > Grade > Section | Old Name | New Name"""
    full = " ".join(context.args)
    parts = [p.strip() for p in full.split("|")]
    if len(parts) != 3:
        await update.message.reply_text(
            "Usage: /editstudent Building > Grade > Section | Old Student Name | New Student Name"
        )
        return
    path_str, old_name, new_name = parts
    result, error = find_class_path(path_str)
    if error:
        await update.message.reply_text(f"❌ {error}")
        return

    conn = db()
    student = conn.execute(
        "SELECT id, name FROM students WHERE section_id = ? AND LOWER(name) = LOWER(?)",
        (result["section_id"], old_name),
    ).fetchone()
    if not student:
        conn.close()
        await update.message.reply_text(f"No student named '{old_name}' found in {result['path']}.")
        return
    conn.execute("UPDATE students SET name = ? WHERE id = ?", (new_name, student["id"]))
    conn.commit()
    conn.close()
    await update.message.reply_text(f"✅ Renamed {old_name} → {new_name} in {result['path']}.")


@require_admin
async def cmd_movestudent(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Move a student to a different class:
    /movestudent Old Building > Old Grade > Old Section | Student Name | New Building > New Grade > New Section"""
    full = " ".join(context.args)
    parts = [p.strip() for p in full.split("|")]
    if len(parts) != 3:
        await update.message.reply_text(
            "Usage: /movestudent Old Building > Old Grade > Old Section | Student Name | "
            "New Building > New Grade > New Section"
        )
        return
    old_path, student_name, new_path = parts
    old_result, error = find_class_path(old_path)
    if error:
        await update.message.reply_text(f"❌ {error}")
        return
    new_result, error = find_class_path(new_path)
    if error:
        await update.message.reply_text(f"❌ New class: {error}")
        return

    conn = db()
    student = conn.execute(
        "SELECT id FROM students WHERE section_id = ? AND LOWER(name) = LOWER(?)",
        (old_result["section_id"], student_name),
    ).fetchone()
    if not student:
        conn.close()
        await update.message.reply_text(f"No student named '{student_name}' found in {old_result['path']}.")
        return
    conn.execute("UPDATE students SET section_id = ? WHERE id = ?", (new_result["section_id"], student["id"]))
    conn.commit()
    conn.close()
    await update.message.reply_text(f"✅ Moved {student_name}: {old_result['path']} → {new_result['path']}.")


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
        f"Give this to the parent(s)/guardian(s) — anyone with the code can send "
        f"/link {link_code} to this bot to get absence notifications.",
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
        await update.message.reply_text(chunk, parse_mode="Markdown", reply_markup=ADMIN_MENU)


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
    students = conn.execute("""
        SELECT students.id, students.name,
               (SELECT COUNT(*) FROM parent_links WHERE parent_links.student_id = students.id) AS guardian_count
        FROM students WHERE section_id = ? ORDER BY students.name
    """, (result["section_id"],)).fetchall()
    conn.close()

    if not students:
        await update.message.reply_text(f"No students in {result['path']} yet.")
        return

    lines = [f"🧑‍🤝‍🧑 {result['path']}:"]
    for s in students:
        gc = s["guardian_count"]
        linked = f"🔗 {gc} guardian(s)" if gc else "⚠️ no guardian linked"
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
    student = conn.execute("""
        SELECT students.name, students.link_code,
               (SELECT COUNT(*) FROM parent_links WHERE parent_links.student_id = students.id) AS guardian_count
        FROM students WHERE section_id = ? AND LOWER(students.name) LIKE LOWER(?)
    """, (result["section_id"], f"%{student_name}%")).fetchone()
    conn.close()

    if not student:
        await update.message.reply_text(f"No student matching '{student_name}' found in {result['path']}.")
        return

    linked = f"{student['guardian_count']} guardian(s) linked" if student["guardian_count"] else "not yet linked"
    await update.message.reply_text(
        f"{student['name']}: code `{student['link_code']}` ({linked})", parse_mode="Markdown"
    )


@require_admin
async def cmd_absentees(update: Update, context: ContextTypes.DEFAULT_TYPE):
    target_date = context.args[0] if context.args else date.today().isoformat()
    await update.message.reply_text(absentees_text(target_date))


# --- Admin button menu: entry points ---

async def admin_btn_add_class(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    context.user_data["admin_flow"] = {"action": "addclass", "step": 0, "data": {}}
    await update.message.reply_text(
        "🏫 What's the building name? (e.g. Main Campus)", reply_markup=FLOW_CANCEL_MENU
    )


async def admin_btn_bulk_classes(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    context.user_data["admin_flow"] = {"action": "bulkclasses", "step": 0, "data": {}}
    await update.message.reply_text(
        "📦 What's the building name? (e.g. Waliya)", reply_markup=FLOW_CANCEL_MENU
    )


async def admin_btn_edit_class(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    sections = get_all_sections()
    if not sections:
        await update.message.reply_text("No classes exist yet. Use ➕ Add Class first.", reply_markup=ADMIN_MENU)
        return
    await update.message.reply_text("✏️ Which class do you want to edit?", reply_markup=build_section_picker(sections, "editclass"))


async def admin_btn_edit_student(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    sections = get_all_sections()
    if not sections:
        await update.message.reply_text("No classes exist yet.", reply_markup=ADMIN_MENU)
        return
    await update.message.reply_text("✏️ Which class is the student in?", reply_markup=build_section_picker(sections, "editstudent"))


async def admin_btn_add_student(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    sections = get_all_sections()
    if not sections:
        await update.message.reply_text("No classes exist yet. Use ➕ Add Class first.", reply_markup=ADMIN_MENU)
        return
    context.user_data["admin_flow"] = {"action": "addstudent", "step": 0, "data": {}}
    await update.message.reply_text("🧑‍🎓 Which class?", reply_markup=build_section_picker(sections, "addstudent"))


async def admin_btn_bulk_students(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    sections = get_all_sections()
    if not sections:
        await update.message.reply_text("No classes exist yet. Use ➕ Add Class first.", reply_markup=ADMIN_MENU)
        return
    await update.message.reply_text(
        "📥 Which class do you want to bulk-add students to?",
        reply_markup=build_section_picker(sections, "bulkstudents"),
    )


async def admin_btn_add_teacher(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    context.user_data["admin_flow"] = {"action": "addteacher", "step": 0, "data": {}}
    await update.message.reply_text(
        "👨‍🏫 Send the teacher's numeric Telegram ID.\n(Ask them to message @userinfobot to find it.)",
        reply_markup=FLOW_CANCEL_MENU,
    )


async def admin_btn_assign_teacher(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    teachers = get_all_teachers()
    if not teachers:
        await update.message.reply_text("No teachers registered yet. Use 👨‍🏫 Add Teacher first.", reply_markup=ADMIN_MENU)
        return
    await update.message.reply_text("🔗 Which teacher?", reply_markup=build_teacher_picker(teachers, "assignteacher"))


async def admin_btn_list_classes(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    await update.message.reply_text(class_tree_text())


async def admin_btn_list_students(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    sections = get_all_sections()
    if not sections:
        await update.message.reply_text("No classes exist yet.", reply_markup=ADMIN_MENU)
        return
    await update.message.reply_text("🧑‍🤝‍🧑 Which class?", reply_markup=build_section_picker(sections, "liststudents"))


async def admin_btn_student_code(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    sections = get_all_sections()
    if not sections:
        await update.message.reply_text("No classes exist yet.", reply_markup=ADMIN_MENU)
        return
    await update.message.reply_text("🔑 Which class is the student in?", reply_markup=build_section_picker(sections, "studentcode"))


async def admin_btn_absentees(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    await update.message.reply_text(absentees_text(date.today().isoformat()))


async def admin_btn_add_admin(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    context.user_data["admin_flow"] = {"action": "addadmin", "step": 0, "data": {}}
    await update.message.reply_text("➕ Send the numeric Telegram ID to make an admin.", reply_markup=FLOW_CANCEL_MENU)


async def admin_btn_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        return
    context.user_data.pop("admin_flow", None)
    pending_bulk_upload.pop(update.effective_user.id, None)
    await update.message.reply_text("Cancelled.", reply_markup=ADMIN_MENU)


# --- Admin button menu: free-text continuation (building/grade/section names,
#     teacher id/name, admin id, student name) ---

async def on_admin_flow_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    if not is_admin(telegram_id):
        return
    flow = context.user_data.get("admin_flow")
    if not flow:
        return  # not mid-flow -- nothing to do with this plain text message

    text = update.message.text.strip()
    action = flow["action"]
    step = flow["step"]
    data = flow["data"]

    if action == "addclass":
        if step == 0:
            data["building"] = text
            flow["step"] = 1
            await update.message.reply_text("📚 What's the grade name? (e.g. Grade 9)", reply_markup=FLOW_CANCEL_MENU)
        elif step == 1:
            data["grade"] = text
            flow["step"] = 2
            await update.message.reply_text("🏷️ What's the section name? (e.g. Section A)", reply_markup=FLOW_CANCEL_MENU)
        elif step == 2:
            data["section"] = text
            path_str = f"{data['building']} > {data['grade']} > {data['section']}"
            result, error = get_or_create_class_path(path_str)
            context.user_data.pop("admin_flow", None)
            if error:
                await update.message.reply_text(f"❌ {error}", reply_markup=ADMIN_MENU)
            else:
                await update.message.reply_text(f"✅ Class ready: {result['path']}", reply_markup=ADMIN_MENU)
        return

    if action == "bulkclasses":
        if step == 0:
            data["building"] = text
            flow["step"] = 1
            await update.message.reply_text("📚 What's the grade name? (e.g. Grade 6)", reply_markup=FLOW_CANCEL_MENU)
        elif step == 1:
            data["grade"] = text
            flow["step"] = 2
            await update.message.reply_text(
                "🏷️ Send the section range, e.g. 'Section A to H' — I'll create one class per letter.\n"
                "(You can also send a single section name if you only need one.)",
                reply_markup=FLOW_CANCEL_MENU,
            )
        elif step == 2:
            section_names = parse_section_range(text) or [text]
            created = []
            for section_name in section_names:
                result, error = get_or_create_class_path(f"{data['building']} > {data['grade']} > {section_name}")
                if not error:
                    created.append(result["path"])
            context.user_data.pop("admin_flow", None)
            if not created:
                await update.message.reply_text("❌ Couldn't create any classes.", reply_markup=ADMIN_MENU)
            else:
                lines = ["✅ Created:"] + [f"  • {p}" for p in created]
                await update.message.reply_text("\n".join(lines), reply_markup=ADMIN_MENU)
        return

    if action == "editclass":
        if step == 0:
            data["new_building"] = text
            flow["step"] = 1
            await update.message.reply_text(
                f"Send the new grade name (currently: {data['old_grade']}). Send the same name to keep it unchanged.",
                reply_markup=FLOW_CANCEL_MENU,
            )
        elif step == 1:
            data["new_grade"] = text
            flow["step"] = 2
            await update.message.reply_text(
                f"Send the new section name (currently: {data['old_section']}). Send the same name to keep it unchanged.",
                reply_markup=FLOW_CANCEL_MENU,
            )
        elif step == 2:
            data["new_section"] = text
            conn = db()
            ok, err_msg = True, ""
            try:
                conn.execute("UPDATE buildings SET name = ? WHERE id = ?", (data["new_building"], data["building_id"]))
                conn.execute("UPDATE grades SET name = ? WHERE id = ?", (data["new_grade"], data["grade_id"]))
                conn.execute("UPDATE sections SET name = ? WHERE id = ?", (data["new_section"], data["section_id"]))
                conn.commit()
            except Exception as e:
                ok, err_msg = False, str(e)
            conn.close()
            context.user_data.pop("admin_flow", None)
            if ok:
                await update.message.reply_text(
                    f"✅ Updated to: {data['new_building']} > {data['new_grade']} > {data['new_section']}",
                    reply_markup=ADMIN_MENU,
                )
            else:
                await update.message.reply_text(f"❌ Couldn't save changes: {err_msg}", reply_markup=ADMIN_MENU)
        return

    if action == "editstudent_rename" and step == 0:
        student_id = data["student_id"]
        old_name = data["old_name"]
        conn = db()
        conn.execute("UPDATE students SET name = ? WHERE id = ?", (text, student_id))
        conn.commit()
        conn.close()
        context.user_data.pop("admin_flow", None)
        await update.message.reply_text(f"✅ Renamed {old_name} → {text}.", reply_markup=ADMIN_MENU)
        return

    if action == "addstudent" and step == 1:
        student_name = text
        section_id = data["section_id"]
        path = data["path"]
        link_code = secrets.token_hex(3).upper()
        conn = db()
        conn.execute(
            "INSERT INTO students (name, section_id, link_code) VALUES (?, ?, ?)",
            (student_name, section_id, link_code),
        )
        conn.commit()
        conn.close()
        context.user_data.pop("admin_flow", None)
        await update.message.reply_text(
            f"✅ Added {student_name} to {path}.\n\nParent link code: `{link_code}`\n"
            f"Give this to the parent(s)/guardian(s) — anyone with the code can send /link {link_code} to this bot.",
            parse_mode="Markdown", reply_markup=ADMIN_MENU,
        )
        return

    if action == "addteacher":
        if step == 0:
            if not text.isdigit():
                await update.message.reply_text("Please send a numeric Telegram ID.", reply_markup=FLOW_CANCEL_MENU)
                return
            data["telegram_id"] = int(text)
            flow["step"] = 1
            await update.message.reply_text("Now send the teacher's name.", reply_markup=FLOW_CANCEL_MENU)
        elif step == 1:
            teacher_name = text
            telegram_id_val = data["telegram_id"]
            conn = db()
            conn.execute(
                "INSERT INTO teachers (telegram_id, name) VALUES (?, ?) ON CONFLICT (telegram_id) DO NOTHING",
                (telegram_id_val, teacher_name),
            )
            conn.commit()
            conn.close()
            context.user_data.pop("admin_flow", None)
            await update.message.reply_text(f"✅ Teacher added: {teacher_name} ({telegram_id_val})", reply_markup=ADMIN_MENU)
        return

    if action == "addadmin" and step == 0:
        if not text.isdigit():
            await update.message.reply_text("Please send a numeric Telegram ID.", reply_markup=FLOW_CANCEL_MENU)
            return
        new_id = int(text)
        conn = db()
        conn.execute("INSERT INTO admins (telegram_id) VALUES (?) ON CONFLICT (telegram_id) DO NOTHING", (new_id,))
        conn.commit()
        conn.close()
        context.user_data.pop("admin_flow", None)
        await update.message.reply_text(f"✅ {new_id} is now an admin.", reply_markup=ADMIN_MENU)
        return


# --- Admin button menu: inline-keyboard picks (class/teacher/student) ---

async def on_admin_pick(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    telegram_id = update.effective_user.id
    if not is_admin(telegram_id):
        await query.answer("Admins only.", show_alert=True)
        return

    parts = query.data.split(":")
    kind = parts[0]

    if kind == "adm_sec":
        action = parts[1]
        if action == "editstudentmove":
            # adm_sec:editstudentmove:<student_id>:<new_section_id>
            move_student_id, section_id = int(parts[2]), int(parts[3])
        else:
            section_id = int(parts[2])
        path = get_section_path(section_id)
        await query.answer()
        if not path:
            await query.message.reply_text("That class no longer exists.", reply_markup=ADMIN_MENU)
            return

        if action == "editstudentmove":
            conn = db()
            old_row = conn.execute("""
                SELECT students.name AS student_name, students.section_id AS old_section_id
                FROM students WHERE students.id = ?
            """, (move_student_id,)).fetchone()
            if not old_row:
                conn.close()
                await query.message.reply_text("That student no longer exists.", reply_markup=ADMIN_MENU)
                return
            old_path = get_section_path(old_row["old_section_id"])
            conn.execute("UPDATE students SET section_id = ? WHERE id = ?", (section_id, move_student_id))
            conn.commit()
            conn.close()
            await query.message.reply_text(
                f"✅ Moved {old_row['student_name']}: {old_path} → {path}", reply_markup=ADMIN_MENU
            )
            return

        if action == "editclass":
            info = get_class_ids_and_names(section_id)
            if not info:
                await query.message.reply_text("That class no longer exists.", reply_markup=ADMIN_MENU)
                return
            context.user_data["admin_flow"] = {
                "action": "editclass", "step": 0,
                "data": {
                    "building_id": info["building_id"], "grade_id": info["grade_id"], "section_id": section_id,
                    "old_building": info["building_name"], "old_grade": info["grade_name"], "old_section": info["section_name"],
                },
            }
            await query.message.reply_text(
                f"✏️ Editing: {info['building_name']} > {info['grade_name']} > {info['section_name']}\n\n"
                f"Send the new building name (currently: {info['building_name']}). Send the same name to keep it unchanged.",
                reply_markup=FLOW_CANCEL_MENU,
            )
            return

        if action == "editstudent":
            students = get_students_in_section(section_id)
            if not students:
                await query.message.reply_text(f"No students in {path} yet.")
                return
            await query.message.reply_text(
                f"✏️ Which student in {path}?", reply_markup=build_student_picker(students, "editstudent")
            )
            return

        if action == "addstudent":
            context.user_data["admin_flow"] = {
                "action": "addstudent", "step": 1, "data": {"section_id": section_id, "path": path}
            }
            await query.message.reply_text(f"🧑‍🎓 Class: {path}\nNow send the student's full name.", reply_markup=FLOW_CANCEL_MENU)
            return

        if action == "bulkstudents":
            pending_bulk_upload[telegram_id] = {"section_id": section_id, "path": path}
            await query.message.reply_text(
                f"📎 Ready. Now upload an Excel (.xlsx), CSV (.csv), or PDF (.pdf) file with one "
                f"student name per row/line — I'll add them all to {path}."
            )
            return

        if action == "liststudents":
            conn = db()
            students = conn.execute("""
                SELECT students.id, students.name,
                       (SELECT COUNT(*) FROM parent_links WHERE parent_links.student_id = students.id) AS guardian_count
                FROM students WHERE section_id = ? ORDER BY students.name
            """, (section_id,)).fetchall()
            conn.close()
            if not students:
                await query.message.reply_text(f"No students in {path} yet.")
                return
            lines = [f"🧑‍🤝‍🧑 {path}:"]
            for s in students:
                gc = s["guardian_count"]
                linked = f"🔗 {gc} guardian(s)" if gc else "⚠️ no guardian linked"
                lines.append(f"  • {s['name']} — {linked}")
            await query.message.reply_text("\n".join(lines))
            return

        if action == "studentcode":
            students = get_students_in_section(section_id)
            if not students:
                await query.message.reply_text(f"No students in {path} yet.")
                return
            await query.message.reply_text(
                f"🔑 Which student in {path}?",
                reply_markup=build_student_picker(students, "studentcode"),
            )
            return

        if action == "assignteacher":
            flow = context.user_data.get("admin_flow")
            if not flow or flow.get("action") != "assignteacher":
                await query.message.reply_text("Session expired — please start over from the menu.", reply_markup=ADMIN_MENU)
                return
            teacher_row_id = flow["data"]["teacher_id"]
            teacher_name = flow["data"]["teacher_name"]
            conn = db()
            conn.execute(
                "INSERT INTO teacher_sections (teacher_id, section_id) VALUES (?, ?) "
                "ON CONFLICT (teacher_id, section_id) DO NOTHING",
                (teacher_row_id, section_id),
            )
            conn.commit()
            conn.close()
            context.user_data.pop("admin_flow", None)
            await query.message.reply_text(f"✅ {teacher_name} assigned to {path}", reply_markup=ADMIN_MENU)
            return
        return

    if kind == "adm_teacher":
        action, teacher_row_id = parts[1], int(parts[2])
        await query.answer()
        if action == "assignteacher":
            conn = db()
            teacher = conn.execute("SELECT name FROM teachers WHERE id = ?", (teacher_row_id,)).fetchone()
            conn.close()
            if not teacher:
                await query.message.reply_text("That teacher no longer exists.", reply_markup=ADMIN_MENU)
                return
            sections = get_all_sections()
            if not sections:
                await query.message.reply_text("No classes exist yet. Use ➕ Add Class first.", reply_markup=ADMIN_MENU)
                return
            context.user_data["admin_flow"] = {
                "action": "assignteacher", "step": 1,
                "data": {"teacher_id": teacher_row_id, "teacher_name": teacher["name"]},
            }
            await query.message.reply_text(
                f"Which class should {teacher['name']} be assigned to?",
                reply_markup=build_section_picker(sections, "assignteacher"),
            )
        return

    if kind == "adm_student":
        action, student_id = parts[1], int(parts[2])
        await query.answer()
        if action == "studentcode":
            conn = db()
            student = conn.execute("SELECT name, link_code FROM students WHERE id = ?", (student_id,)).fetchone()
            guardian_count = 0
            if student:
                guardian_count = conn.execute(
                    "SELECT COUNT(*) AS c FROM parent_links WHERE student_id = ?", (student_id,)
                ).fetchone()["c"]
            conn.close()
            if not student:
                await query.message.reply_text("That student no longer exists.", reply_markup=ADMIN_MENU)
                return
            linked = f"{guardian_count} guardian(s) linked" if guardian_count else "not yet linked"
            await query.message.reply_text(
                f"{student['name']}: code `{student['link_code']}` ({linked})",
                parse_mode="Markdown", reply_markup=ADMIN_MENU,
            )
            return

        if action == "editstudent":
            conn = db()
            student = conn.execute("SELECT name FROM students WHERE id = ?", (student_id,)).fetchone()
            conn.close()
            if not student:
                await query.message.reply_text("That student no longer exists.", reply_markup=ADMIN_MENU)
                return
            buttons = InlineKeyboardMarkup([
                [InlineKeyboardButton("✏️ Rename", callback_data=f"adm_editact:rename:{student_id}")],
                [InlineKeyboardButton("↔ Move to Another Class", callback_data=f"adm_editact:move:{student_id}")],
            ])
            await query.message.reply_text(f"What do you want to do with {student['name']}?", reply_markup=buttons)
            return
        return


async def on_admin_editact(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the Rename / Move choice shown after picking a student to edit."""
    query = update.callback_query
    if not is_admin(update.effective_user.id):
        await query.answer("Admins only.", show_alert=True)
        return

    _, act, student_id_str = query.data.split(":")
    student_id = int(student_id_str)
    await query.answer()

    conn = db()
    student = conn.execute("SELECT name FROM students WHERE id = ?", (student_id,)).fetchone()
    conn.close()
    if not student:
        await query.message.reply_text("That student no longer exists.", reply_markup=ADMIN_MENU)
        return

    if act == "rename":
        context.user_data["admin_flow"] = {
            "action": "editstudent_rename", "step": 0,
            "data": {"student_id": student_id, "old_name": student["name"]},
        }
        await query.message.reply_text(f"Send the new name for {student['name']}.", reply_markup=FLOW_CANCEL_MENU)
        return

    if act == "move":
        sections = get_all_sections()
        if not sections:
            await query.message.reply_text("No classes exist yet. Use ➕ Add Class first.", reply_markup=ADMIN_MENU)
            return
        await query.message.reply_text(
            f"Which class should {student['name']} move to?",
            reply_markup=build_section_picker_with_extra(sections, "editstudentmove", student_id),
        )
        return


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

    # Notify every linked guardian of absent/late students (not just one).
    for student_id, status in session["statuses"].items():
        if status == "present":
            continue
        row = conn.execute("SELECT name FROM students WHERE id = ?", (student_id,)).fetchone()
        if not row:
            continue
        guardians = conn.execute(
            "SELECT chat_id FROM parent_links WHERE student_id = ?", (student_id,)
        ).fetchall()
        if not guardians:
            continue
        message = notification_text(row["name"], status, session["section_path"], session["date"])
        for g in guardians:
            try:
                await context.bot.send_message(chat_id=g["chat_id"], text=message)
            except Exception as e:
                print(f"[notify] Failed to notify guardian {g['chat_id']} of student {student_id}: {e}")
    conn.close()


# --- Parent linking ---

async def try_link_parent(update: Update, code: str):
    code = code.strip().upper()
    chat_id = update.effective_chat.id

    conn = db()
    student = conn.execute("SELECT id, name FROM students WHERE link_code = ?", (code,)).fetchone()
    if not student:
        await update.message.reply_text("❌ That code isn't valid. Please double-check it with the school.")
        conn.close()
        return

    already = conn.execute(
        "SELECT 1 FROM parent_links WHERE student_id = ? AND chat_id = ?", (student["id"], chat_id)
    ).fetchone()
    if already:
        await update.message.reply_text(f"You're already linked to {student['name']}.")
        conn.close()
        return

    conn.execute(
        "INSERT INTO parent_links (student_id, chat_id) VALUES (?, ?) ON CONFLICT (student_id, chat_id) DO NOTHING",
        (student["id"], chat_id),
    )
    conn.commit()
    conn.close()

    await update.message.reply_text(
        f"✅ Linked! You'll now be notified here if {student['name']} is marked absent or late.\n\n"
        f"Other family members can link too — just send the same code with /link."
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
    app.add_handler(CommandHandler("menu", cmd_menu))
    app.add_handler(CommandHandler("help", cmd_help))
    app.add_handler(CommandHandler("addadmin", cmd_addadmin))
    app.add_handler(CommandHandler("addclass", cmd_addclass))
    app.add_handler(CommandHandler("addclasses", cmd_addclasses))
    app.add_handler(CommandHandler("editclass", cmd_editclass))
    app.add_handler(CommandHandler("editstudent", cmd_editstudent))
    app.add_handler(CommandHandler("movestudent", cmd_movestudent))
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

    # Callback (inline button) handlers
    app.add_handler(CallbackQueryHandler(on_attendance_button, pattern="^(att|attsubmit):"))
    app.add_handler(CallbackQueryHandler(on_pickclass, pattern="^pickclass:"))
    app.add_handler(CallbackQueryHandler(on_admin_pick, pattern="^adm_(sec|teacher|student):"))
    app.add_handler(CallbackQueryHandler(on_admin_editact, pattern="^adm_editact:"))

    # Teacher reply-keyboard button
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(MY_CLASSES_LABEL)}$"), on_myclasses_button_text))

    # Admin reply-keyboard buttons (checked before the generic flow-text handler)
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_ADD_CLASS)}$"), admin_btn_add_class))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_BULK_CLASSES)}$"), admin_btn_bulk_classes))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_EDIT_CLASS)}$"), admin_btn_edit_class))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_ADD_STUDENT)}$"), admin_btn_add_student))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_BULK_STUDENTS)}$"), admin_btn_bulk_students))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_EDIT_STUDENT)}$"), admin_btn_edit_student))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_ADD_TEACHER)}$"), admin_btn_add_teacher))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_ASSIGN_TEACHER)}$"), admin_btn_assign_teacher))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_LIST_CLASSES)}$"), admin_btn_list_classes))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_LIST_STUDENTS)}$"), admin_btn_list_students))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_STUDENT_CODE)}$"), admin_btn_student_code))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_ABSENTEES)}$"), admin_btn_absentees))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_ADD_ADMIN)}$"), admin_btn_add_admin))
    app.add_handler(MessageHandler(filters.Regex(f"^{re.escape(BTN_CANCEL)}$"), admin_btn_cancel))

    # Generic continuation handler for admin flows -- lower priority group so
    # the exact-match button handlers above always win first.
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_admin_flow_text), group=1)

    # File uploads for bulk student import
    app.add_handler(MessageHandler(filters.Document.ALL, on_document))

    print("School attendance bot running.")
    app.run_polling()


if __name__ == "__main__":
    main()
