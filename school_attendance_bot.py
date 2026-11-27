"""
School Attendance Bot (python-telegram-bot v20+)
-----------------------------------------------
A Telegram bot for schools: teachers take attendance from their phone,
parents get notified instantly (in Amharic or English), and the whole school
structure (buildings, grades, sections, students, teachers) is built up
THROUGH the bot -- nothing needs to be configured in advance.

WHAT'S NEW IN THIS VERSION
  * Ethiopian calendar everywhere users see a date (stored internally as
    standard ISO dates, converted only for display / input).
  * Amharic (default) or English, chosen per user with the 🌐 button.
  * Teachers register themselves with /start -- the bot reads their Telegram
    ID automatically and sends the admins an Approve / Reject request.
    Approval is mandatory.
  * Weekly report, sent automatically every Friday (teachers: own classes,
    admins: whole school) and on demand.
  * Remove class / remove student (with a confirmation that shows which data
    will be deleted too).
  * Exam results for teachers (max score set per exam, editable later).
  * Extra features:
      - parents are told when a child is marked present again after absent
      - teachers can edit today's attendance after submitting
      - monthly attendance % per student with a low-attendance warning
      - parents can submit an excuse for an absence
      - admin announcements (all parents / one class / all teachers)
      - export a class report to Excel or PDF
      - daily reminder to teachers who haven't taken attendance
      - homework / behavior notes from teachers to parents

RUNS 24/7 WHEN DEPLOYED (e.g. Render, Railway):
  - Opens a tiny HTTP server on $PORT so free "Web Service" tiers accept it.
  - Build Command:  pip install -r requirements.txt
  - Start Command:  python school_attendance_bot.py

ENVIRONMENT VARIABLES:
    TG_BOT_TOKEN          (from @BotFather)                       REQUIRED
    DATABASE_URL          Postgres connection string (recommended for
                          deployment; otherwise local SQLite is used)
    DB_PATH               SQLite file, only if DATABASE_URL is not set
    LOW_ATTENDANCE_PCT    warning threshold, default 80
    WEEKLY_REPORT_TIME    Friday report time, EAT, default 16:00
    REMINDER_TIME         weekday reminder time, EAT, default 09:30
    PDF_FONT_PATH         optional .ttf with Ethiopic glyphs (e.g.
                          NotoSansEthiopic-Regular.ttf) so Amharic names
                          show correctly inside exported PDFs

FIRST RUN:
  The very first person to send /start becomes the first admin.
"""

import os
import io
import re
import csv
import html
import sqlite3
import secrets
import threading
from datetime import datetime, date, time as dtime, timedelta, timezone
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
LOW_ATTENDANCE_PCT = float(os.environ.get("LOW_ATTENDANCE_PCT", "80"))
PDF_FONT_PATH = os.environ.get("PDF_FONT_PATH", "").strip()

if USE_POSTGRES:
    import psycopg2
    import psycopg2.extras

STATUS_CYCLE = ["present", "absent", "late"]
STATUS_EMOJI = {"present": "✅", "absent": "❌", "late": "🕒"}
NAME_HEADER_WORDS = {"name", "student", "student name", "full name", "students", "ስም", "ተማሪ"}

# Ethiopia has no daylight saving: EAT is always UTC+3.
EAT = timezone(timedelta(hours=3))


# ======================================================================
# Ethiopian calendar
# ======================================================================

ET_MONTHS = {
    "am": ["መስከረም", "ጥቅምት", "ኅዳር", "ታኅሣሥ", "ጥር", "የካቲት", "መጋቢት",
           "ሚያዝያ", "ግንቦት", "ሰኔ", "ሐምሌ", "ነሐሴ", "ጳጉሜን"],
    "en": ["Meskerem", "Tikimt", "Hidar", "Tahsas", "Tir", "Yekatit", "Megabit",
           "Miazia", "Ginbot", "Sene", "Hamle", "Nehasse", "Pagume"],
}
_ETH_EPOCH = 1723856


def now_eat() -> datetime:
    return datetime.now(EAT)


def today_greg() -> date:
    return now_eat().date()


def today_iso() -> str:
    return today_greg().isoformat()


def _greg_to_jdn(y, m, d):
    a = (14 - m) // 12
    yy = y + 4800 - a
    mm = m + 12 * a - 3
    return d + (153 * mm + 2) // 5 + 365 * yy + yy // 4 - yy // 100 + yy // 400 - 32045


def _jdn_to_greg(jdn) -> date:
    a = jdn + 32044
    b = (4 * a + 3) // 146097
    c = a - (146097 * b) // 4
    d = (4 * c + 3) // 1461
    e = c - (1461 * d) // 4
    m = (5 * e + 2) // 153
    day = e - (153 * m + 2) // 5 + 1
    month = m + 3 - 12 * (m // 10)
    year = 100 * b + d - 4800 + m // 10
    return date(year, month, day)


def greg_to_eth(d: date):
    """Gregorian date -> (eth_year, eth_month, eth_day)."""
    jdn = _greg_to_jdn(d.year, d.month, d.day)
    r = (jdn - _ETH_EPOCH) % 1461
    n = (r % 365) + 365 * (r // 1460)
    year = 4 * ((jdn - _ETH_EPOCH) // 1461) + r // 365 - r // 1460
    return year, n // 30 + 1, n % 30 + 1


def eth_to_greg(y, m, d) -> date:
    jdn = _ETH_EPOCH + 365 + 365 * (y - 1) + y // 4 + 30 * m + d - 31
    return _jdn_to_greg(jdn)


def eth_days_in_month(y, m) -> int:
    if m <= 12:
        return 30
    return 6 if y % 4 == 3 else 5


def parse_eth_date(text: str):
    """'2019-03-15' typed as an ETHIOPIAN date -> ISO (Gregorian) string, or None."""
    m = re.match(r"^\s*(\d{4})[-/.](\d{1,2})[-/.](\d{1,2})\s*$", text or "")
    if not m:
        return None
    y, mo, d = (int(x) for x in m.groups())
    if not (1 <= mo <= 13) or not (1 <= d <= eth_days_in_month(y, mo)):
        return None
    try:
        return eth_to_greg(y, mo, d).isoformat()
    except ValueError:
        return None


def fmt_date(iso: str, lang="am") -> str:
    """ISO (Gregorian) -> '12 መስከረም 2019' (Ethiopian)."""
    y, m, d = greg_to_eth(date.fromisoformat(iso))
    return f"{d} {ET_MONTHS[lang][m - 1]} {y}"


def eth_month_range(iso: str):
    """(first_day_iso, last_day_iso) of the Ethiopian month containing iso."""
    y, m, _ = greg_to_eth(date.fromisoformat(iso))
    start = eth_to_greg(y, m, 1)
    end = start + timedelta(days=eth_days_in_month(y, m) - 1)
    return start.isoformat(), end.isoformat()


def eth_month_label(iso: str, lang="am") -> str:
    y, m, _ = greg_to_eth(date.fromisoformat(iso))
    return f"{ET_MONTHS[lang][m - 1]} {y}"


def parse_hhmm(value: str, default: str) -> dtime:
    try:
        h, m = (int(x) for x in (value or default).split(":"))
        return dtime(hour=h, minute=m, tzinfo=EAT)
    except Exception:
        h, m = (int(x) for x in default.split(":"))
        return dtime(hour=h, minute=m, tzinfo=EAT)


def fmt_num(v) -> str:
    return "—" if v is None else f"{v:g}"


def parse_number(text: str):
    try:
        v = float(text.strip().replace(",", "."))
    except (ValueError, AttributeError):
        return None
    if v != v or v in (float("inf"), float("-inf")):
        return None
    return v


# ======================================================================
# Translations (Amharic is the default; English available via 🌐)
# ======================================================================

STR = {
    # ---- welcome / menus ----
    "welcome_first_admin": {
        "am": "👋 እንኳን በደህና መጡ! እስካሁን አስተዳዳሪ ስላልነበረ እርስዎ የመጀመሪያው አስተዳዳሪ ሆነዋል።\n\nለመጀመር ከታች ያሉትን አዝራሮች ይጠቀሙ፤ ሙሉውን የትዕዛዝ ዝርዝር ለማየት /help ይላኩ።",
        "en": "👋 Welcome! No admin existed yet, so you're now the first admin.\n\nUse the buttons below to get started, or send /help for the full command list."},
    "welcome_admin": {
        "am": "እንኳን ደህና መጡ፣ አስተዳዳሪ። ከታች ያሉትን አዝራሮች ይጠቀሙ፤ ትዕዛዞችን ለማየት /help ይላኩ።",
        "en": "Welcome back, admin. Use the buttons below, or /help for commands."},
    "welcome_teacher": {
        "am": "👋 እንኳን ደህና መጡ! ክፍሎችዎን ለማየት፣ ክትትል ለመያዝ እና የፈተና ውጤት ለማስገባት ከታች ያሉትን አዝራሮች ይጠቀሙ።",
        "en": "👋 Welcome back! Use the buttons below to take attendance, enter exam results and more."},
    "welcome_parent": {
        "am": "👋 እንኳን ደህና መጡ! ከታች ባሉት አዝራሮች የልጅዎን ክትትል ማየት እና የቀረበትን ምክንያት ማሳወቅ ይችላሉ።",
        "en": "👋 Welcome back! Use the buttons below to see your child's attendance or send an excuse."},
    "welcome_new": {
        "am": "👋 እንኳን ደህና መጡ!\n\n• ወላጅ ወይም አሳዳጊ ከሆኑ፦ ትምህርት ቤቱ የሰጠዎትን ኮድ በ /link ኮድ ብለው ይላኩ።\n• መምህር ከሆኑ፦ ከታች ያለውን አዝራር ይጫኑ። አስተዳዳሪው ጥያቄዎን ካጸደቀ በኋላ መጠቀም ይችላሉ።",
        "en": "👋 Welcome!\n\n• Parents/guardians: send /link <code> with the code the school gave you.\n• Teachers: tap the button below. You can start once an admin approves your request."},
    "menu_admin": {"am": "የአስተዳዳሪ ምናሌ፦", "en": "Admin menu:"},
    "menu_teacher": {"am": "የመምህር ምናሌ፦", "en": "Teacher menu:"},
    "menu_parent": {"am": "የወላጅ ምናሌ፦", "en": "Parent menu:"},
    "menu_none": {"am": "ምንም የሚታይ ነገር የለም። ወላጆች /link ኮድ ይጠቀሙ።",
                  "en": "Nothing to show yet. Parents: use /link <code>."},
    "choose_language": {"am": "ቋንቋ ይምረጡ፦ / Choose a language:", "en": "Choose a language: / ቋንቋ ይምረጡ፦"},
    "language_set": {"am": "✅ ቋንቋ ወደ አማርኛ ተቀይሯል።", "en": "✅ Language set to English."},
    "cancelled": {"am": "ተሰርዟል።", "en": "Cancelled."},
    "generic_error": {"am": "ይቅርታ፣ ችግር ተፈጥሯል። እባክዎ እንደገና ይሞክሩ።", "en": "Sorry, something went wrong. Please try again."},
    "help_general": {
        "am": "/menu - ምናሌውን እንደገና አሳይ\n/language - ቋንቋ ቀይር\n/myclasses - የእኔ ክፍሎች (መምህራን)\n/attendance Building > Grade > Section - ክፍሉን በመጻፍ ክትትል ያዙ\n/weekly - ሳምንታዊ ሪፖርት\n/link ኮድ - ወላጆች ከልጅ ጋር ይገናኙ (ከአንድ በላይ አሳዳጊ መገናኘት ይችላል)",
        "en": "/menu - show your menu again\n/language - change language\n/myclasses - your classes (teachers)\n/attendance Building > Grade > Section - take attendance by typing the class\n/weekly - weekly report\n/link <code> - parents: link to a child (several guardians per child are fine)"},
    "help_admin": {
        "am": "የአስተዳዳሪ ትዕዛዞች፦\n/addadmin id\n/addclass Building > Grade > Section\n/addclasses Building > Grade > Section A to H\n/editclass Old Path | New Path\n/removeclass Building > Grade > Section\n/addstudent Path | Student Name\n/addstudents Path (ከዚያ ፋይል ይላኩ)\n/editstudent Path | Old Name | New Name\n/movestudent Old Path | Name | New Path\n/removestudent Path | Student Name\n/addteacher id Name\n/assignteacher id Path\n/listclasses\n/liststudents Path\n/studentcode Path | Student Name\n/absentees [ዓመት-ወር-ቀን በኢትዮጵያ አቆጣጠር፣ ለምሳሌ 2019-03-18]",
        "en": "Admin commands:\n/addadmin id\n/addclass Building > Grade > Section\n/addclasses Building > Grade > Section A to H\n/editclass Old Path | New Path\n/removeclass Building > Grade > Section\n/addstudent Path | Student Name\n/addstudents Path (then upload a file)\n/editstudent Path | Old Name | New Name\n/movestudent Old Path | Name | New Path\n/removestudent Path | Student Name\n/addteacher id Name\n/assignteacher id Path\n/listclasses\n/liststudents Path\n/studentcode Path | Student Name\n/absentees [YYYY-MM-DD in the Ethiopian calendar, e.g. 2019-03-18]"},

    # ---- teacher registration ----
    "btn_request_teacher": {"am": "👨‍🏫 መምህር ነኝ — ፈቃድ ጠይቅ", "en": "👨‍🏫 I'm a teacher — request access"},
    "teacher_req_sent": {"am": "✅ ጥያቄዎ ለአስተዳዳሪው ተልኳል። ሲጸድቅ መልዕክት ይደርስዎታል። እናመሰግናለን!",
                         "en": "✅ Your request was sent to the admins. You'll get a message once it's approved. Thank you!"},
    "teacher_req_already": {"am": "ጥያቄዎ ቀድሞ ተልኳል፤ እባክዎ የአስተዳዳሪውን ውሳኔ በትዕግስት ይጠብቁ።",
                            "en": "Your request was already sent. Please wait for an admin's decision."},
    "teacher_already": {"am": "እርስዎ ቀድሞውኑ የተመዘገቡ ነዎት።", "en": "You're already registered."},
    "admin_new_request": {
        "am": "🆕 አዲስ የመምህርነት ጥያቄ\n\nስም፦ {name}\nUsername፦ {username}\nTelegram ID፦ {tid}\n\nያጸድቁታል?",
        "en": "🆕 New teacher request\n\nName: {name}\nUsername: {username}\nTelegram ID: {tid}\n\nApprove?"},
    "btn_approve": {"am": "✅ አጽድቅ", "en": "✅ Approve"},
    "btn_reject": {"am": "❌ ውድቅ አድርግ", "en": "❌ Reject"},
    "teacher_approved_admin": {"am": "✅ {name} ({tid}) እንደ መምህር ጸድቋል።", "en": "✅ {name} ({tid}) was approved as a teacher."},
    "teacher_rejected_admin": {"am": "❌ የ{name} ({tid}) ጥያቄ ውድቅ ተደርጓል።", "en": "❌ The request from {name} ({tid}) was rejected."},
    "teacher_approved_user": {
        "am": "🎉 እንኳን ደስ አለዎት! ጥያቄዎ ጸድቋል። አሁን መምህር ሆነው መጠቀም ይችላሉ። ክፍል እስኪመደብልዎ ድረስ እባክዎ ይጠብቁ።",
        "en": "🎉 Congratulations! Your request was approved. You can now use the bot as a teacher. Please wait until an admin assigns your classes."},
    "teacher_rejected_user": {
        "am": "ይቅርታ፣ የመምህርነት ጥያቄዎ አልጸደቀም። ለበለጠ መረጃ እባክዎ የትምህርት ቤቱን አስተዳደር ያነጋግሩ።",
        "en": "Sorry, your teacher request was not approved. Please contact the school administration for more information."},
    "request_handled": {"am": "ይህ ጥያቄ ቀድሞ ተስተናግዷል።", "en": "This request has already been handled."},
    "no_pending": {"am": "በመጠባበቅ ላይ ያለ የመምህር ጥያቄ የለም።", "en": "There are no pending teacher requests."},
    "teacher_added": {"am": "✅ መምህር ተጨምሯል፦ {name} ({id})", "en": "✅ Teacher added: {name} ({id})"},
    "teacher_unknown": {"am": "ይህ መምህር ገና አልተመዘገበም — መጀመሪያ ጥያቄውን ያጽድቁ ወይም /addteacher ይጠቀሙ።",
                        "en": "That teacher isn't registered yet — approve their request or use /addteacher first."},
    "teacher_gone": {"am": "ይህ መምህር አልተገኘም።", "en": "That teacher no longer exists."},
    "no_teachers_yet": {"am": "እስካሁን የተመዘገበ መምህር የለም። መምህራን /start ብለው ጥያቄ ይላኩ።",
                        "en": "No teachers registered yet. Teachers should send /start and request access."},
    "teacher_assigned": {"am": "✅ {name} ወደ {path} ተመድበዋል።", "en": "✅ {name} assigned to {path}"},
    "which_teacher": {"am": "🔗 የትኛውን መምህር?", "en": "🔗 Which teacher?"},
    "which_class_for_teacher": {"am": "{name} ወደ የትኛው ክፍል ይመደቡ?", "en": "Which class should {name} be assigned to?"},

    # ---- generic ----
    "admin_only": {"am": "ይህ ትዕዛዝ ለአስተዳዳሪዎች ብቻ ነው።", "en": "This command is admin-only."},
    "admins_only_alert": {"am": "ለአስተዳዳሪዎች ብቻ።", "en": "Admins only."},
    "not_teacher": {"am": "እርስዎ እንደ መምህር አልተመዘገቡም። እባክዎ /start ብለው ፈቃድ ይጠይቁ።",
                    "en": "You're not registered as a teacher. Please send /start and request access."},
    "not_assigned": {"am": "ይህ ክፍል አልተመደበልዎትም።", "en": "You're not assigned to this class."},
    "session_expired": {"am": "ጊዜው አልፏል — እባክዎ ከምናሌው እንደገና ይጀምሩ።", "en": "Session expired — please start over from the menu."},
    "err_format": {"am": "ቅርጸቱ እንዲህ መሆን አለበት፦ Building > Grade > Section", "en": "Format must be: Building > Grade > Section"},
    "err_class_missing": {"am": "'{path}' የሚል ክፍል አልተገኘም። ፊደሉን ያረጋግጡ ወይም መጀመሪያ /addclass ይጠቀሙ።",
                          "en": "No class found matching '{path}'. Check the spelling or use /addclass first."},
    "err_range": {"am": "እንደ 'Section A to H' ያለ የፊደል ርዝመት አልተገኘም። ለአንድ ክፍል /addclass ይጠቀሙ።",
                  "en": "Couldn't find a letter range like 'Section A to H'. For a single class, use /addclass."},
    "save_failed": {"am": "❌ ለውጦቹን ማስቀመጥ አልተቻለም፦ {err}", "en": "❌ Couldn't save changes: {err}"},
    "bad_eth_date": {"am": "❌ ቀኑ በኢትዮጵያ አቆጣጠር እንዲህ መጻፍ አለበት፦ ዓመት-ወር-ቀን (ለምሳሌ 2019-03-18)",
                     "en": "❌ Please write the date in the Ethiopian calendar as YYYY-MM-DD (e.g. 2019-03-18)."},
    "need_name": {"am": "እባክዎ ከ '|' በኋላ የተማሪውን ስም ያስገቡ።", "en": "Please include the student's name after '|'."},
    "need_numeric_id": {"am": "እባክዎ የቁጥር Telegram ID ይላኩ።", "en": "Please send a numeric Telegram ID."},
    "need_positive_number": {"am": "እባክዎ ከ0 የሚበልጥ ቁጥር ያስገቡ።", "en": "Please send a number greater than 0."},
    "admin_added": {"am": "✅ {id} አሁን አስተዳዳሪ ነው።", "en": "✅ {id} is now an admin."},
    "ask_admin_id": {"am": "➕ አስተዳዳሪ ለማድረግ የሰውየውን የቁጥር Telegram ID ይላኩ።", "en": "➕ Send the numeric Telegram ID to make an admin."},

    # ---- classes ----
    "ask_building": {"am": "🏫 የህንፃው ስም ማን ነው? (ለምሳሌ፦ Waliya)", "en": "🏫 What's the building name? (e.g. Waliya)"},
    "ask_grade": {"am": "📚 የክፍል ደረጃው ስም ማን ነው? (ለምሳሌ፦ Grade 6)", "en": "📚 What's the grade name? (e.g. Grade 6)"},
    "ask_section": {"am": "🏷️ የክፍሉ (ሴክሽን) ስም ማን ነው? (ለምሳሌ፦ Section A)", "en": "🏷️ What's the section name? (e.g. Section A)"},
    "ask_section_range": {
        "am": "🏷️ የሴክሽን ክልሉን ይላኩ፤ ለምሳሌ 'Section A to H' — ለእያንዳንዱ ፊደል አንድ ክፍል እፈጥራለሁ።\n(አንድ ክፍል ብቻ ከፈለጉ አንድ ስም ይላኩ።)",
        "en": "🏷️ Send the section range, e.g. 'Section A to H' — I'll add one class per letter.\n(Or send a single section name if you only need one.)"},
    "class_ready": {"am": "✅ ክፍል ተጨምሯል፦ {path}", "en": "✅ Class added: {path}"},
    "classes_ready": {"am": "✅ ክፍሎች ተጨምረዋል፦", "en": "✅ Classes added:"},
    "no_class_created": {"am": "❌ ምንም ክፍል መጨመር አልተቻለም።", "en": "❌ Couldn't add any classes."},
    "class_updated": {"am": "✅ ወደ {path} ተሻሽሏል።", "en": "✅ Updated to: {path}"},
    "class_gone": {"am": "ይህ ክፍል አሁን የለም።", "en": "That class no longer exists."},
    "no_classes_yet": {"am": "እስካሁን ምንም ክፍል የለም። ለመጀመር ➕ ክፍል ጨምር ይጠቀሙ።", "en": "No classes set up yet. Use ➕ Add Class to start."},
    "no_classes_admin": {"am": "እስካሁን ምንም ክፍል የለም። መጀመሪያ ክፍል ይጨምሩ።", "en": "No classes exist yet. Add a class first."},
    "no_classes_for_you": {"am": "እስካሁን ምንም ክፍል አልተመደበልዎትም። እባክዎ አስተዳዳሪውን ያነጋግሩ።",
                           "en": "You're not assigned to any classes yet. Please ask an admin."},
    "tree_section": {"am": "{name} ({n} ተማሪዎች)", "en": "{name} ({n} students)"},
    "which_class": {"am": "🏫 የትኛው ክፍል?", "en": "🏫 Which class?"},
    "which_class_edit": {"am": "✏️ የትኛውን ክፍል ማስተካከል ይፈልጋሉ?", "en": "✏️ Which class do you want to edit?"},
    "which_class_remove": {"am": "🗑 የትኛውን ክፍል ማስወገድ ይፈልጋሉ?", "en": "🗑 Which class do you want to remove?"},
    "which_class_student": {"am": "🧑‍🎓 ተማሪው በየትኛው ክፍል ነው?", "en": "🧑‍🎓 Which class is the student in?"},
    "tap_class_attendance": {"am": "ክትትል ለመጀመር ክፍል ይምረጡ፦", "en": "Tap a class to start attendance:"},
    "ask_new_building": {
        "am": "✏️ በማስተካከል ላይ፦ {path}\n\nአዲሱን የህንፃ ስም ይላኩ (አሁን፦ {old})። ለማቆየት ተመሳሳዩን ስም ይላኩ።",
        "en": "✏️ Editing: {path}\n\nSend the new building name (currently: {old}). Send the same name to keep it."},
    "ask_new_grade": {"am": "አዲሱን የክፍል ደረጃ ስም ይላኩ (አሁን፦ {old})። ለማቆየት ተመሳሳዩን ይላኩ።",
                      "en": "Send the new grade name (currently: {old}). Send the same name to keep it."},
    "ask_new_section": {"am": "አዲሱን የሴክሽን ስም ይላኩ (አሁን፦ {old})። ለማቆየት ተመሳሳዩን ይላኩ።",
                        "en": "Send the new section name (currently: {old}). Send the same name to keep it."},
    "confirm_del_class": {
        "am": "⚠️ ክፍሉን ለማስወገድ እርግጠኛ ነዎት?\n\n{path}\n\nከክፍሉ ጋር የሚከተሉት መረጃዎች ለዘላለም ይሰረዛሉ፦\n• {students} ተማሪዎች\n• {attendance} የክትትል መዝገቦች\n• {exams} ፈተናዎች (ከነውጤታቸው)\n• {links} የወላጅ ግንኙነቶች\n• የመምህራን ምደባ\n\nይህ ሊመለስ አይችልም።",
        "en": "⚠️ Are you sure you want to remove this class?\n\n{path}\n\nThe following data will be permanently deleted with it:\n• {students} students\n• {attendance} attendance records\n• {exams} exams (with their results)\n• {links} guardian links\n• teacher assignments\n\nThis cannot be undone."},
    "class_removed": {"am": "✅ ክፍሉ ከመረጃው ጋር ተወግዷል፦ {path}", "en": "✅ Class and its data removed: {path}"},
    "btn_yes_delete": {"am": "🗑 አዎ፣ ከመረጃው ጋር አስወግድ", "en": "🗑 Yes, delete with all data"},
    "btn_no": {"am": "↩️ አይ፣ ተመለስ", "en": "↩️ No, go back"},

    # ---- students ----
    "which_student": {"am": "🧑‍🎓 በ{path} ውስጥ የትኛው ተማሪ?", "en": "🧑‍🎓 Which student in {path}?"},
    "ask_student_name": {"am": "🧑‍🎓 ክፍል፦ {path}\nአሁን የተማሪውን ሙሉ ስም ይላኩ።", "en": "🧑‍🎓 Class: {path}\nNow send the student's full name."},
    "student_added": {
        "am": "✅ {name} ወደ {path} ተጨምሯል።\n\nየወላጅ ማገናኛ ኮድ፦ <code>{code}</code>\nይህን ኮድ ለወላጆች/አሳዳጊዎች ይስጡ — ማንኛውም ሰው <code>/link {code}</code> ብሎ ቢልክ የመቅረት ማሳወቂያ ይደርሰዋል።",
        "en": "✅ Added {name} to {path}.\n\nParent link code: <code>{code}</code>\nGive this to the parent(s)/guardian(s) — anyone can send <code>/link {code}</code> to this bot to get absence notifications."},
    "students_added_head": {"am": "✅ {n} ተማሪዎች ወደ {path} ተጨምረዋል፦", "en": "✅ Added {n} students to {path}:"},
    "student_gone": {"am": "ይህ ተማሪ አሁን የለም።", "en": "That student no longer exists."},
    "student_not_found": {"am": "'{name}' የሚባል ተማሪ በ{path} ውስጥ አልተገኘም።", "en": "No student named '{name}' found in {path}."},
    "student_renamed": {"am": "✅ {old} → {new} ተሰይሟል።", "en": "✅ Renamed {old} → {new}."},
    "student_moved": {"am": "✅ {name} ተዛውሯል፦ {old} → {new}", "en": "✅ Moved {name}: {old} → {new}"},
    "student_removed": {"am": "✅ {name} ከመረጃው ጋር ተወግዷል።", "en": "✅ {name} and their data were removed."},
    "student_what_do": {"am": "በ{name} ላይ ምን ማድረግ ይፈልጋሉ?", "en": "What do you want to do with {name}?"},
    "btn_rename": {"am": "✏️ ስም ቀይር", "en": "✏️ Rename"},
    "btn_move": {"am": "↔ ወደ ሌላ ክፍል አዛውር", "en": "↔ Move to Another Class"},
    "ask_new_student_name": {"am": "ለ{name} አዲሱን ስም ይላኩ።", "en": "Send the new name for {name}."},
    "move_to_which": {"am": "{name} ወደ የትኛው ክፍል ይዛወር?", "en": "Which class should {name} move to?"},
    "confirm_del_student": {
        "am": "⚠️ {name}ን ለማስወገድ እርግጠኛ ነዎት?\n\nየሚከተሉት መረጃዎች ለዘላለም ይሰረዛሉ፦\n• {attendance} የክትትል መዝገቦች\n• {scores} የፈተና ውጤቶች\n• {links} የወላጅ ግንኙነቶች\n\nይህ ሊመለስ አይችልም።",
        "en": "⚠️ Are you sure you want to remove {name}?\n\nThe following data will be permanently deleted:\n• {attendance} attendance records\n• {scores} exam scores\n• {links} guardian links\n\nThis cannot be undone."},
    "no_students_in": {"am": "በ{path} ውስጥ እስካሁን ተማሪ የለም።", "en": "No students in {path} yet."},
    "no_students_short": {"am": "እስካሁን ተማሪ የለም።", "en": "No students yet."},
    "student_linked": {"am": "{name} — 🔗 {n} አሳዳጊ(ዎች)", "en": "{name} — 🔗 {n} guardian(s)"},
    "student_unlinked": {"am": "{name} — ⚠️ አሳዳጊ አልተገናኘም", "en": "{name} — ⚠️ no guardian linked"},
    "student_code": {"am": "{name}፦ ኮድ <code>{code}</code> ({status})", "en": "{name}: code <code>{code}</code> ({status})"},
    "linked_n": {"am": "{n} አሳዳጊ(ዎች) ተገናኝተዋል", "en": "{n} guardian(s) linked"},
    "not_linked": {"am": "ገና አልተገናኘም", "en": "not yet linked"},
    "upload_ready": {
        "am": "📎 ዝግጁ ነኝ። አሁን የተማሪዎችን ስም (በአንድ ረድፍ/መስመር አንድ ስም) የያዘ Excel (.xlsx)፣ CSV (.csv) ወይም PDF (.pdf) ፋይል ይላኩ — ሁሉንም ወደ {path} እጨምራለሁ።",
        "en": "📎 Ready. Now upload an Excel (.xlsx), CSV (.csv), or PDF (.pdf) file with one student name per row/line — I'll add them all to {path}."},
    "bad_file_type": {"am": "❌ ይህ የፋይል አይነት አይደገፍም። እባክዎ .xlsx፣ .csv ወይም .pdf ይላኩ።", "en": "❌ Unsupported file type. Please send a .xlsx, .csv, or .pdf file."},
    "file_read_failed": {"am": "❌ ፋይሉን ማንበብ አልተቻለም፦ {err}", "en": "❌ Couldn't read that file: {err}"},
    "no_names_found": {"am": "❌ በፋይሉ ውስጥ የተማሪ ስም አልተገኘም። እያንዳንዱ ስም በራሱ ረድፍ (Excel/CSV) ወይም መስመር (PDF) መሆኑን ያረጋግጡ።",
                       "en": "❌ No student names found. Make sure each name is in its own row (Excel/CSV) or line (PDF)."},
    "link_invalid": {"am": "❌ ይህ ኮድ ትክክል አይደለም። እባክዎ ከትምህርት ቤቱ ጋር ያረጋግጡ።", "en": "❌ That code isn't valid. Please double-check it with the school."},
    "link_already": {"am": "እርስዎ ቀድሞውኑ ከ{name} ጋር ተገናኝተዋል።", "en": "You're already linked to {name}."},
    "link_ok": {
        "am": "✅ ተገናኝቷል! {name} ሲቀር ወይም ሲዘገይ እዚህ መልዕክት ይደርስዎታል።\n\nሌሎች የቤተሰብ አባላትም ተመሳሳዩን ኮድ በ /link በመላክ መገናኘት ይችላሉ።",
        "en": "✅ Linked! You'll be notified here if {name} is marked absent or late.\n\nOther family members can link too — just send the same code with /link."},

    # ---- attendance & notifications ----
    "att_header": {"am": "📋 የ{path} ክትትል — {date}\nስም ሲነኩ ይቀየራል፦ የተገኘ → የቀረ → የዘገየ። ሁሉም በመጀመሪያ 'የተገኘ' ናቸው።",
                   "en": "📋 Attendance for {path} — {date}\nTap a name to cycle Present → Absent → Late. Everyone starts as Present."},
    "att_editing": {"am": "✏️ የዛሬው ክትትል ቀድሞ ተመዝግቧል — እያስተካከሉ ነው።", "en": "✏️ Today's attendance was already submitted — you're editing it."},
    "btn_submit_att": {"am": "✅ ክትትሉን አስገባ", "en": "✅ Submit Attendance"},
    "att_expired": {"am": "ይህ የክትትል ክፍለ ጊዜ አልቋል።", "en": "This attendance session has expired."},
    "submitting": {"am": "በማስገባት ላይ...", "en": "Submitting..."},
    "att_submitted": {"am": "✅ የ{path} ክትትል ገብቷል — {date}", "en": "✅ Attendance submitted for {path} — {date}"},
    "att_low_head": {"am": "⚠️ ከ{thr}% በታች የሆነ የወሩ ክትትል፦", "en": "⚠️ Monthly attendance below {thr}%:"},
    "notify_absent": {
        "am": "❌ ውድ ወላጅ/አሳዳጊ፣ {name} ዛሬ በ{path} ({date}) ቀሪ ተብሎ ተመዝግቧል።\n\nእባክዎ ልጅዎን ያነጋግሩ ወይም ያረጋግጡ። ለምክንያት ማሳወቅ ከፈለጉ ከምናሌው '📝 ምክንያት አስገባ' ይጠቀሙ። እናመሰግናለን።",
        "en": "❌ Dear parent/guardian, {name} was marked ABSENT today in {path} ({date}).\n\nPlease check in with your child. To explain the absence, use '📝 Submit Excuse' in the menu. Thank you."},
    "notify_late": {
        "am": "🕒 ውድ ወላጅ/አሳዳጊ፣ {name} ዛሬ በ{path} ({date}) ዘግይቶ እንደመጣ ተመዝግቧል።\n\nበሰዓቱ እንዲደርስ እባክዎ ያስታውሱት። እናመሰግናለን።",
        "en": "🕒 Dear parent/guardian, {name} was marked LATE today in {path} ({date}).\n\nA gentle reminder about arriving on time would help. Thank you."},
    "notify_back": {
        "am": "✅ ውድ ወላጅ/አሳዳጊ፣ የ{name} ዛሬ ({date}) ክትትል ተስተካክሏል — አሁን 'ተገኝቷል' ተብሎ ተመዝግቧል። ለተፈጠረው ግራ መጋባት ይቅርታ እንጠይቃለን።",
        "en": "✅ Dear parent/guardian, the record for {name} today ({date}) was corrected — they are now marked PRESENT. Sorry for any worry caused."},
    "notify_low": {
        "am": "⚠️ ማሳሰቢያ፦ የ{name} የዚህ ወር የክትትል መጠን {pct}% ነው፤ ከሚጠበቀው {thr}% በታች ነው። እባክዎ ልጅዎ በየቀኑ እንዲገኝ ይደግፉት።",
        "en": "⚠️ Reminder: {name}'s attendance this month is {pct}%, below the expected {thr}%. Please help your child attend every day."},
    "reminder": {"am": "⏰ ትዝታ፦ ዛሬ ({date}) የክትትል መዝገብ ያልያዙባቸው ክፍሎች፦", "en": "⏰ Reminder: you haven't taken attendance today ({date}) for:"},
    "absentees_head": {"am": "📋 የ{date} ቀሪዎች/ያረፈዱ፦", "en": "📋 Absentees/late for {date}:"},
    "absentees_none": {"am": "ለ{date} የተመዘገበ ቀሪ/ዘግይቶ የመጣ የለም።", "en": "No absences/lates recorded for {date}."},

    # ---- weekly / monthly ----
    "weekly_head": {"am": "📊 ሳምንታዊ ሪፖርት — {path}\n🗓 {start} – {end}", "en": "📊 Weekly report — {path}\n🗓 {start} – {end}"},
    "weekly_no_data": {"am": "በዚህ ሳምንት የተመዘገበ ክትትል የለም።", "en": "No attendance was recorded this week."},
    "weekly_summary": {"am": "ክትትል የተያዘባቸው ቀናት፦ {days}\nየክፍሉ የተገኝነት መጠን፦ {pct}%", "en": "Days recorded: {days}\nClass attendance: {pct}%"},
    "weekly_line": {"am": "{name} — ቀሪ {absent}፣ ዘግይቶ {late}፣ በምክንያት {excused} ({pct}%)",
                    "en": "{name} — absent {absent}, late {late}, excused {excused} ({pct}%)"},
    "weekly_perfect": {"am": "🎉 በዚህ ሳምንት ሁሉም ተማሪዎች ሙሉ በሙሉ ተገኝተዋል!", "en": "🎉 Every student had perfect attendance this week!"},
    "monthly_head": {"am": "📈 ወርሃዊ ክትትል — {path}\n🗓 {month}", "en": "📈 Monthly attendance — {path}\n🗓 {month}"},
    "monthly_legend": {"am": "✅ ተገኝቷል 🕒 ዘግይቷል ❌ ቀርቷል 📝 በምክንያት። ⚠️ = ከ{thr}% በታች",
                       "en": "✅ present 🕒 late ❌ absent 📝 excused. ⚠️ = below {thr}%"},
    "monthly_low_count": {"am": "⚠️ ዝቅተኛ ክትትል ያላቸው ተማሪዎች፦ {n}", "en": "⚠️ Students with low attendance: {n}"},
    "child_line": {
        "am": "👦 {name} — {path}\n🗓 {month}፦ ✅ {present} 🕒 {late} ❌ {absent} 📝 {excused}\nየተገኝነት መጠን፦ {pct}%",
        "en": "👦 {name} — {path}\n🗓 {month}: ✅ {present} 🕒 {late} ❌ {absent} 📝 {excused}\nAttendance: {pct}%"},
    "child_low": {"am": "⚠️ ከሚጠበቀው {thr}% በታች ነው። እባክዎ ልጅዎ በየቀኑ እንዲገኝ ይደግፉት።",
                  "en": "⚠️ Below the expected {thr}%. Please help your child attend every day."},
    "no_children": {"am": "እስካሁን ከምንም ልጅ ጋር አልተገናኙም። /link ኮድ ይጠቀሙ።", "en": "You aren't linked to any child yet. Use /link <code>."},

    # ---- excuses ----
    "excuse_which_child": {"am": "ለየትኛው ልጅ?", "en": "Which child?"},
    "excuse_none": {"am": "በቅርብ ጊዜ የተመዘገበ መቅረት ወይም ማርፈድ የለም።", "en": "There are no recent absences or lates to explain."},
    "excuse_which_date": {"am": "ለየትኛው ቀን ምክንያት ማሳወቅ ይፈልጋሉ?", "en": "Which day do you want to explain?"},
    "excuse_ask_reason": {"am": "📝 የ{date} መቅረት/ማርፈድ ምክንያቱን ይጻፉ።", "en": "📝 Please write the reason for the absence/lateness on {date}."},
    "excuse_saved": {"am": "✅ ምክንያቱ ተመዝግቦ ለመምህራን ተልኳል። እናመሰግናለን!", "en": "✅ Your excuse was saved and sent to the teachers. Thank you!"},
    "excuse_to_teacher": {"am": "📝 ከወላጅ የደረሰ ምክንያት\nተማሪ፦ {name}\nቀን፦ {date}\nምክንያት፦ {reason}",
                          "en": "📝 Excuse from a parent\nStudent: {name}\nDate: {date}\nReason: {reason}"},

    # ---- announcements & notes ----
    "ann_who": {"am": "📢 ማስታወቂያው ለማን ይላክ?", "en": "📢 Who should receive the announcement?"},
    "ann_all_parents": {"am": "👨‍👩‍👧 ለሁሉም ወላጆች", "en": "👨‍👩‍👧 All parents"},
    "ann_one_class": {"am": "🏫 ለአንድ ክፍል ወላጆች", "en": "🏫 One class's parents"},
    "ann_teachers": {"am": "👨‍🏫 ለሁሉም መምህራን", "en": "👨‍🏫 All teachers"},
    "ann_ask_text": {"am": "✍️ የማስታወቂያውን ጽሑፍ ይላኩ።", "en": "✍️ Send the announcement text."},
    "ann_ask_text_class": {"am": "✍️ ለ{path} ወላጆች የሚላከውን ማስታወቂያ ይጻፉ።", "en": "✍️ Write the announcement for the parents of {path}."},
    "ann_sent": {"am": "✅ ማስታወቂያው ለ{n} ሰዎች ተልኳል።", "en": "✅ Announcement sent to {n} people."},
    "announce_msg": {"am": "📢 ከትምህርት ቤቱ የተላከ ማስታወቂያ፦\n\n{text}", "en": "📢 Announcement from the school:\n\n{text}"},
    "note_who": {"am": "💬 በ{path} ውስጥ መልዕክቱ ለማን ይላክ?", "en": "💬 In {path}, who is the message for?"},
    "note_whole_class": {"am": "👥 ለክፍሉ ወላጆች ሁሉ (የቤት ስራ)", "en": "👥 Whole class (homework)"},
    "note_kind": {"am": "የመልዕክቱ አይነት ምንድን ነው?", "en": "What kind of message is it?"},
    "kind_hw": {"am": "📚 የቤት ስራ", "en": "📚 Homework"},
    "kind_beh": {"am": "⚠️ የባህሪ ማስታወሻ", "en": "⚠️ Behavior note"},
    "kind_good": {"am": "👍 መልካም ዜና", "en": "👍 Good news"},
    "note_ask_hw_class": {"am": "✍️ ለክፍሉ ወላጆች የሚላከውን የቤት ስራ ይጻፉ።", "en": "✍️ Write the homework to send to the class's parents."},
    "note_ask_text": {"am": "✍️ መልዕክቱን ይጻፉ።", "en": "✍️ Write the message."},
    "note_sent": {"am": "✅ መልዕክቱ ለ{n} አሳዳጊዎች ተልኳል።", "en": "✅ Message sent to {n} guardian(s)."},
    "note_hw_class": {"am": "📚 የቤት ስራ — {path}\nከመምህር {teacher}፦\n\n{text}", "en": "📚 Homework — {path}\nFrom {teacher}:\n\n{text}"},
    "note_hw": {"am": "📚 የ{name} የቤት ስራ\nከመምህር {teacher}፦\n\n{text}", "en": "📚 Homework for {name}\nFrom {teacher}:\n\n{text}"},
    "note_beh": {"am": "⚠️ ስለ {name} የባህሪ ማስታወሻ\nከመምህር {teacher}፦\n\n{text}", "en": "⚠️ Behavior note about {name}\nFrom {teacher}:\n\n{text}"},
    "note_good": {"am": "👍 ስለ {name} መልካም ዜና\nከመምህር {teacher}፦\n\n{text}", "en": "👍 Good news about {name}\nFrom {teacher}:\n\n{text}"},

    # ---- export ----
    "export_choose": {"am": "📤 የ{path} ወርሃዊ ሪፖርት በየትኛው ቅርጸት ይላክ?", "en": "📤 Which format for the monthly report of {path}?"},
    "preparing": {"am": "በማዘጋጀት ላይ...", "en": "Preparing..."},
    "export_failed": {"am": "❌ ፋይሉን ማዘጋጀት አልተቻለም፦ {err}", "en": "❌ Couldn't prepare the file: {err}"},
    "xl_attendance": {"am": "ክትትል", "en": "Attendance"},
    "xl_exams": {"am": "ፈተናዎች", "en": "Exams"},
    "col_student": {"am": "ተማሪ", "en": "Student"},
    "col_present": {"am": "ተገኝቷል", "en": "Present"},
    "col_absent": {"am": "ቀርቷል", "en": "Absent"},
    "col_late": {"am": "ዘግይቷል", "en": "Late"},
    "col_excused": {"am": "በምክንያት", "en": "Excused"},
    "col_pct": {"am": "መጠን %", "en": "Attendance %"},

    # ---- exams ----
    "exam_menu": {"am": "📝 የፈተና ውጤት — ምን ማድረግ ይፈልጋሉ?", "en": "📝 Exam results — what would you like to do?"},
    "btn_new_exam": {"am": "➕ አዲስ ፈተና", "en": "➕ New Exam"},
    "btn_my_exams": {"am": "📂 ፈተናዎች (እይ/አስተካክል)", "en": "📂 Exams (view/edit)"},
    "ask_exam_name": {"am": "📝 ክፍል፦ {path}\nየፈተናውን ስም ይላኩ (ለምሳሌ፦ Mid-term).", "en": "📝 Class: {path}\nSend the exam name (e.g. Mid-term)."},
    "ask_exam_subject": {"am": "📖 የትምህርቱን ስም ይላኩ (ለምሳሌ፦ Mathematics)።", "en": "📖 Send the subject (e.g. Mathematics)."},
    "ask_exam_max": {"am": "🔢 ለዚህ ፈተና ከፍተኛውን ውጤት ይላኩ (ለምሳሌ፦ 100)።", "en": "🔢 Send the maximum score for this exam (e.g. 100)."},
    "exam_ask_score": {"am": "👤 {n}/{total} — {name}\nውጤት ያስገቡ (ከ{max})፦", "en": "👤 {n}/{total} — {name}\nEnter the score (out of {max}):"},
    "btn_skip": {"am": "⏭ ዝለል", "en": "⏭ Skip"},
    "btn_finish": {"am": "🏁 ጨርስ", "en": "🏁 Finish"},
    "score_invalid": {"am": "❌ ውጤቱ ከ0 እስከ {max} ያለ ቁጥር መሆን አለበት። እንደገና ይሞክሩ።", "en": "❌ The score must be a number from 0 to {max}. Please try again."},
    "score_saved": {"am": "✅ ውጤቱ ተቀምጧል።", "en": "✅ Score saved."},
    "exam_done": {"am": "✅ የፈተና ውጤቶች ተቀምጠዋል። ውጤት ለማስተካከል ተማሪውን ይንኩ።", "en": "✅ Exam results saved. Tap a student to edit their score."},
    "exam_detail": {
        "am": "📝 {subject} — {name}\n🏫 {path}\n🗓 {date}\nከፍተኛ ውጤት፦ {max}\nአማካይ፦ {avg}\nየገቡ ውጤቶች፦ {entered}/{total}\n\nውጤት ለማስተካከል ተማሪውን ይንኩ፦",
        "en": "📝 {subject} — {name}\n🏫 {path}\n🗓 {date}\nMax score: {max}\nAverage: {avg}\nScores entered: {entered}/{total}\n\nTap a student to edit their score:"},
    "btn_change_max": {"am": "🔧 ከፍተኛ ውጤቱን ቀይር", "en": "🔧 Change max score"},
    "exam_edit_ask": {"am": "✏️ ለ{name} አዲሱን ውጤት ያስገቡ (ከ{max})፦", "en": "✏️ Enter the new score for {name} (out of {max}):"},
    "max_too_low": {"am": "❌ አዲሱ ከፍተኛ ውጤት ከገባው ከፍተኛ ውጤት ({top}) መብለጥ ወይም እኩል መሆን አለበት።",
                    "en": "❌ The new maximum can't be lower than the highest entered score ({top})."},
    "max_updated": {"am": "✅ ከፍተኛው ውጤት ተሻሽሏል።", "en": "✅ Maximum score updated."},
    "no_exams": {"am": "እስካሁን ምንም ፈተና የለም።", "en": "No exams yet."},
    "pick_exam": {"am": "ፈተና ይምረጡ፦", "en": "Pick an exam:"},
    "exam_gone": {"am": "ይህ ፈተና አሁን የለም።", "en": "That exam no longer exists."},
}


# ======================================================================
# Reply-keyboard buttons
# ======================================================================

BTN = {
    "add_class": {"am": "➕ ክፍል ጨምር", "en": "➕ Add Class"},
    "bulk_classes": {"am": "📦 ብዙ ክፍሎች ጨምር", "en": "📦 Bulk Add Classes"},
    "edit_class": {"am": "✏️ ክፍል አስተካክል", "en": "✏️ Edit Class"},
    "del_class": {"am": "🗑 ክፍል አስወግድ", "en": "🗑 Remove Class"},
    "add_student": {"am": "🧑‍🎓 ተማሪ ጨምር", "en": "🧑‍🎓 Add Student"},
    "bulk_students": {"am": "📥 ብዙ ተማሪዎች ጨምር", "en": "📥 Bulk Add Students"},
    "edit_student": {"am": "✏️ ተማሪ አስተካክል", "en": "✏️ Edit Student"},
    "del_student": {"am": "🗑 ተማሪ አስወግድ", "en": "🗑 Remove Student"},
    "pending_teachers": {"am": "🕒 የመምህር ጥያቄዎች", "en": "🕒 Teacher Requests"},
    "assign_teacher": {"am": "🔗 መምህር መድብ", "en": "🔗 Assign Teacher"},
    "list_classes": {"am": "📚 ክፍሎችን ዘርዝር", "en": "📚 List Classes"},
    "list_students": {"am": "🧑‍🤝‍🧑 ተማሪዎችን ዘርዝር", "en": "🧑‍🤝‍🧑 List Students"},
    "student_code": {"am": "🔑 የተማሪ ኮድ", "en": "🔑 Student Code"},
    "absentees": {"am": "📋 የዛሬ ቀሪዎች", "en": "📋 Absentees Today"},
    "weekly": {"am": "📊 ሳምንታዊ ሪፖርት", "en": "📊 Weekly Report"},
    "monthly": {"am": "📈 ወርሃዊ ክትትል", "en": "📈 Monthly Attendance"},
    "export": {"am": "📤 ሪፖርት አውጣ", "en": "📤 Export Report"},
    "announce": {"am": "📢 ማስታወቂያ", "en": "📢 Announcement"},
    "add_admin": {"am": "➕ አስተዳዳሪ ጨምር", "en": "➕ Add Admin"},
    "language": {"am": "🌐 ቋንቋ / Language", "en": "🌐 ቋንቋ / Language"},
    "cancel": {"am": "❌ ሰርዝ", "en": "❌ Cancel"},
    "my_classes": {"am": "📋 የእኔ ክፍሎች", "en": "📋 My Classes"},
    "exams": {"am": "📝 የፈተና ውጤት", "en": "📝 Exam Results"},
    "notes": {"am": "💬 ለወላጆች መልዕክት", "en": "💬 Notes to Parents"},
    "p_children": {"am": "📊 የልጆቼ ክትትል", "en": "📊 My Children"},
    "p_excuse": {"am": "📝 ምክንያት አስገባ", "en": "📝 Submit Excuse"},
}

ROLE_LAYOUT = {
    "admin": [
        ["add_class", "bulk_classes"], ["edit_class", "del_class"],
        ["add_student", "bulk_students"], ["edit_student", "del_student"],
        ["pending_teachers", "assign_teacher"], ["list_classes", "list_students"],
        ["student_code", "absentees"], ["weekly", "monthly"],
        ["export", "announce"], ["my_classes", "exams"], ["notes", "add_admin"],
        ["language", "cancel"],
    ],
    "teacher": [
        ["my_classes", "exams"], ["notes", "weekly"],
        ["monthly", "export"], ["language", "cancel"],
    ],
    "parent": [["p_children", "p_excuse"], ["language"]],
}

LABEL_TO_KEY = {label: key for key, labels in BTN.items() for label in labels.values()}


def tr(lang, key, **kw) -> str:
    entry = STR.get(key)
    if not entry:
        return key
    text = entry.get(lang) or entry["en"]
    return text.format(**kw) if kw else text


def menu_for(role, lang):
    layout = ROLE_LAYOUT.get(role)
    if not layout:
        return None
    return ReplyKeyboardMarkup([[BTN[k][lang] for k in row] for row in layout], resize_keyboard=True)


def cancel_menu(lang):
    return ReplyKeyboardMarkup([[BTN["cancel"][lang]]], resize_keyboard=True)


# ======================================================================
# Health-check HTTP server (for free-tier "Web Service" hosting)
# ======================================================================

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


# ======================================================================
# Database (SQLite locally, Postgres in production via DATABASE_URL)
# SQL is written with "?" placeholders; converted to "%s" for Postgres.
# ======================================================================

class _PGConnWrapper:
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
        return _PGConnWrapper(psycopg2.connect(DATABASE_URL))
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def fetchall(sql, params=()):
    conn = db()
    try:
        return conn.execute(sql, params).fetchall()
    finally:
        conn.close()


def fetchone(sql, params=()):
    conn = db()
    try:
        return conn.execute(sql, params).fetchone()
    finally:
        conn.close()


def execute(sql, params=()):
    conn = db()
    try:
        conn.execute(sql, params)
        conn.commit()
    finally:
        conn.close()


def init_db():
    conn = db()
    id_type = "SERIAL PRIMARY KEY" if USE_POSTGRES else "INTEGER PRIMARY KEY AUTOINCREMENT"

    conn.execute("CREATE TABLE IF NOT EXISTS admins (telegram_id BIGINT PRIMARY KEY)")
    conn.execute(f"CREATE TABLE IF NOT EXISTS buildings (id {id_type}, name TEXT UNIQUE)")
    conn.execute(f"""CREATE TABLE IF NOT EXISTS grades (
        id {id_type}, name TEXT, building_id INTEGER REFERENCES buildings(id),
        UNIQUE(name, building_id))""")
    conn.execute(f"""CREATE TABLE IF NOT EXISTS sections (
        id {id_type}, name TEXT, grade_id INTEGER REFERENCES grades(id),
        UNIQUE(name, grade_id))""")
    conn.execute(f"""CREATE TABLE IF NOT EXISTS students (
        id {id_type}, name TEXT, section_id INTEGER REFERENCES sections(id),
        link_code TEXT UNIQUE, parent_chat_id BIGINT)""")
    conn.execute(f"""CREATE TABLE IF NOT EXISTS teachers (
        id {id_type}, telegram_id BIGINT UNIQUE, name TEXT)""")
    conn.execute("""CREATE TABLE IF NOT EXISTS teacher_sections (
        teacher_id INTEGER REFERENCES teachers(id),
        section_id INTEGER REFERENCES sections(id),
        UNIQUE(teacher_id, section_id))""")
    conn.execute(f"""CREATE TABLE IF NOT EXISTS attendance (
        id {id_type}, student_id INTEGER REFERENCES students(id),
        date TEXT, status TEXT, marked_by BIGINT, marked_at TEXT,
        UNIQUE(student_id, date))""")
    conn.execute(f"""CREATE TABLE IF NOT EXISTS parent_links (
        id {id_type}, student_id INTEGER REFERENCES students(id),
        chat_id BIGINT, UNIQUE(student_id, chat_id))""")

    # --- new in this version ---
    conn.execute("CREATE TABLE IF NOT EXISTS user_prefs (chat_id BIGINT PRIMARY KEY, lang TEXT)")
    conn.execute("""CREATE TABLE IF NOT EXISTS pending_teachers (
        telegram_id BIGINT PRIMARY KEY, name TEXT, username TEXT, requested_at TEXT)""")
    conn.execute(f"""CREATE TABLE IF NOT EXISTS exams (
        id {id_type}, section_id INTEGER REFERENCES sections(id),
        name TEXT, subject TEXT, max_score REAL, exam_date TEXT, created_by BIGINT)""")
    conn.execute("""CREATE TABLE IF NOT EXISTS exam_scores (
        exam_id INTEGER REFERENCES exams(id),
        student_id INTEGER REFERENCES students(id),
        score REAL, UNIQUE(exam_id, student_id))""")
    conn.execute(f"""CREATE TABLE IF NOT EXISTS excuses (
        id {id_type}, student_id INTEGER REFERENCES students(id),
        date TEXT, reason TEXT, chat_id BIGINT, created_at TEXT,
        UNIQUE(student_id, date))""")
    conn.commit()

    # carry forward the old single parent_chat_id into parent_links
    conn.execute("""
        INSERT INTO parent_links (student_id, chat_id)
        SELECT id, parent_chat_id FROM students
        WHERE parent_chat_id IS NOT NULL
        ON CONFLICT (student_id, chat_id) DO NOTHING
    """)
    conn.commit()
    conn.close()
    print(f"[db] Using {'Postgres' if USE_POSTGRES else 'SQLite (' + DB_PATH + ')'}")


# ======================================================================
# Roles & language
# ======================================================================

def is_admin(uid: int) -> bool:
    return fetchone("SELECT 1 FROM admins WHERE telegram_id = ?", (uid,)) is not None


def any_admin_exists() -> bool:
    return fetchone("SELECT 1 FROM admins LIMIT 1") is not None


def is_teacher(uid: int) -> bool:
    return fetchone("SELECT 1 FROM teachers WHERE telegram_id = ?", (uid,)) is not None


def is_parent(uid: int) -> bool:
    return fetchone("SELECT 1 FROM parent_links WHERE chat_id = ?", (uid,)) is not None


def role_of(uid: int) -> str:
    if is_admin(uid):
        return "admin"
    if is_teacher(uid):
        return "teacher"
    if is_parent(uid):
        return "parent"
    return "none"


def get_admin_ids():
    return [r["telegram_id"] for r in fetchall("SELECT telegram_id FROM admins")]


_lang_cache = {}


def get_lang(uid: int) -> str:
    if uid in _lang_cache:
        return _lang_cache[uid]
    row = fetchone("SELECT lang FROM user_prefs WHERE chat_id = ?", (uid,))
    lang = row["lang"] if row and row["lang"] in ("am", "en") else "am"
    _lang_cache[uid] = lang
    return lang


def set_lang(uid: int, lang: str):
    execute(
        "INSERT INTO user_prefs (chat_id, lang) VALUES (?, ?) "
        "ON CONFLICT (chat_id) DO UPDATE SET lang = excluded.lang", (uid, lang))
    _lang_cache[uid] = lang


# ======================================================================
# Class path helpers ("Building > Grade > Section")
# Helpers return (result, error_key); error_key is a translation key.
# ======================================================================

def parse_path(path_str: str):
    parts = [p.strip() for p in path_str.split(">")]
    if len(parts) != 3 or not all(parts):
        return None
    return tuple(parts)


def _get_or_create(conn, sel_sql, sel_params, ins_sql, ins_params):
    row = conn.execute(sel_sql, sel_params).fetchone()
    if not row:
        conn.execute(ins_sql, ins_params)
        conn.commit()
        row = conn.execute(sel_sql, sel_params).fetchone()
    return row["id"]


def get_or_create_class_path(path_str: str):
    parsed = parse_path(path_str)
    if not parsed:
        return None, "err_format"
    building_name, grade_name, section_name = parsed
    conn = db()
    try:
        b_id = _get_or_create(
            conn, "SELECT id FROM buildings WHERE LOWER(name) = LOWER(?)", (building_name,),
            "INSERT INTO buildings (name) VALUES (?)", (building_name,))
        g_id = _get_or_create(
            conn, "SELECT id FROM grades WHERE LOWER(name) = LOWER(?) AND building_id = ?", (grade_name, b_id),
            "INSERT INTO grades (name, building_id) VALUES (?, ?)", (grade_name, b_id))
        s_id = _get_or_create(
            conn, "SELECT id FROM sections WHERE LOWER(name) = LOWER(?) AND grade_id = ?", (section_name, g_id),
            "INSERT INTO sections (name, grade_id) VALUES (?, ?)", (section_name, g_id))
    finally:
        conn.close()
    return {"section_id": s_id, "path": f"{building_name} > {grade_name} > {section_name}"}, None


_FIND_CLASS_SQL = """
    SELECT buildings.id AS building_id, grades.id AS grade_id, sections.id AS section_id
    FROM sections
    JOIN grades ON sections.grade_id = grades.id
    JOIN buildings ON grades.building_id = buildings.id
    WHERE LOWER(buildings.name) = LOWER(?) AND LOWER(grades.name) = LOWER(?) AND LOWER(sections.name) = LOWER(?)
"""


def find_class_path(path_str: str):
    parsed = parse_path(path_str)
    if not parsed:
        return None, "err_format"
    row = fetchone(_FIND_CLASS_SQL, parsed)
    if not row:
        return None, "err_class_missing"
    return {"section_id": row["section_id"], "path": path_str}, None


def find_class_ids(path_str: str):
    parsed = parse_path(path_str)
    if not parsed:
        return None, "err_format"
    row = fetchone(_FIND_CLASS_SQL, parsed)
    if not row:
        return None, "err_class_missing"
    return {"building_id": row["building_id"], "grade_id": row["grade_id"], "section_id": row["section_id"]}, None


def parse_section_range(section_str: str):
    """'Section A to H' / 'Section A-H' -> ['Section A', ..., 'Section H'] (or None)."""
    m = re.match(r'^(.*?)\s*([A-Za-z])\s*(?:to|-)\s*([A-Za-z])\s*$', section_str.strip(), re.IGNORECASE)
    if not m:
        return None
    prefix, a, b = m.groups()
    a, b = ord(a.upper()), ord(b.upper())
    if a > b or (b - a) > 25:
        return None
    prefix = prefix.strip()
    return [f"{prefix} {chr(c)}".strip() if prefix else chr(c) for c in range(a, b + 1)]


def get_class_ids_and_names(section_id: int):
    return fetchone("""
        SELECT buildings.id AS building_id, buildings.name AS building_name,
               grades.id AS grade_id, grades.name AS grade_name, sections.name AS section_name
        FROM sections
        JOIN grades ON sections.grade_id = grades.id
        JOIN buildings ON grades.building_id = buildings.id
        WHERE sections.id = ?
    """, (section_id,))


def get_section_path(section_id: int):
    row = get_class_ids_and_names(section_id)
    if not row:
        return None
    return f"{row['building_name']} > {row['grade_name']} > {row['section_name']}"


_SECTION_LIST_SQL = """
    SELECT sections.id AS section_id, buildings.name AS building_name,
           grades.name AS grade_name, sections.name AS section_name
    FROM sections
    JOIN grades ON sections.grade_id = grades.id
    JOIN buildings ON grades.building_id = buildings.id
"""


def get_all_sections():
    return fetchall(_SECTION_LIST_SQL + " ORDER BY building_name, grade_name, section_name")


def sections_for_user(uid: int):
    """Admins see every class; teachers only the ones assigned to them."""
    if is_admin(uid):
        return get_all_sections()
    t = fetchone("SELECT id FROM teachers WHERE telegram_id = ?", (uid,))
    if not t:
        return []
    return fetchall(
        _SECTION_LIST_SQL +
        " WHERE sections.id IN (SELECT section_id FROM teacher_sections WHERE teacher_id = ?)"
        " ORDER BY building_name, grade_name, section_name", (t["id"],))


def can_access_section(uid: int, section_id: int) -> bool:
    if is_admin(uid):
        return True
    t = fetchone("SELECT id FROM teachers WHERE telegram_id = ?", (uid,))
    if not t:
        return False
    return fetchone(
        "SELECT 1 FROM teacher_sections WHERE teacher_id = ? AND section_id = ?",
        (t["id"], section_id)) is not None


def get_all_teachers():
    return fetchall("SELECT id, telegram_id, name FROM teachers ORDER BY name")


def get_students_in_section(section_id):
    return fetchall("SELECT id, name FROM students WHERE section_id = ? ORDER BY name", (section_id,))


def create_student(section_id: int, name: str) -> str:
    while True:
        code = secrets.token_hex(3).upper()
        if not fetchone("SELECT 1 FROM students WHERE link_code = ?", (code,)):
            break
    execute("INSERT INTO students (name, section_id, link_code) VALUES (?, ?, ?)", (name, section_id, code))
    return code


def sender_name(uid: int) -> str:
    row = fetchone("SELECT name FROM teachers WHERE telegram_id = ?", (uid,))
    return row["name"] if row else "Admin"


# ======================================================================
# Deleting classes / students (children first, so foreign keys are happy)
# ======================================================================

def delete_student_data(conn, student_id: int):
    conn.execute("DELETE FROM attendance WHERE student_id = ?", (student_id,))
    conn.execute("DELETE FROM parent_links WHERE student_id = ?", (student_id,))
    conn.execute("DELETE FROM excuses WHERE student_id = ?", (student_id,))
    conn.execute("DELETE FROM exam_scores WHERE student_id = ?", (student_id,))
    conn.execute("DELETE FROM students WHERE id = ?", (student_id,))


def delete_student(student_id: int):
    conn = db()
    try:
        delete_student_data(conn, student_id)
        conn.commit()
    finally:
        conn.close()


def delete_class(section_id: int):
    info = get_class_ids_and_names(section_id)
    sub = "(SELECT id FROM students WHERE section_id = ?)"
    conn = db()
    try:
        conn.execute(f"DELETE FROM attendance WHERE student_id IN {sub}", (section_id,))
        conn.execute(f"DELETE FROM parent_links WHERE student_id IN {sub}", (section_id,))
        conn.execute(f"DELETE FROM excuses WHERE student_id IN {sub}", (section_id,))
        conn.execute(f"DELETE FROM exam_scores WHERE student_id IN {sub}", (section_id,))
        conn.execute("DELETE FROM exam_scores WHERE exam_id IN (SELECT id FROM exams WHERE section_id = ?)", (section_id,))
        conn.execute("DELETE FROM exams WHERE section_id = ?", (section_id,))
        conn.execute("DELETE FROM students WHERE section_id = ?", (section_id,))
        conn.execute("DELETE FROM teacher_sections WHERE section_id = ?", (section_id,))
        conn.execute("DELETE FROM sections WHERE id = ?", (section_id,))
        if info:
            conn.execute(
                "DELETE FROM grades WHERE id = ? AND NOT EXISTS (SELECT 1 FROM sections WHERE grade_id = ?)",
                (info["grade_id"], info["grade_id"]))
            conn.execute(
                "DELETE FROM buildings WHERE id = ? AND NOT EXISTS (SELECT 1 FROM grades WHERE building_id = ?)",
                (info["building_id"], info["building_id"]))
        conn.commit()
    finally:
        conn.close()
    for token in [t for t, s in pending_attendance.items() if s["section_id"] == section_id]:
        pending_attendance.pop(token, None)


def class_data_counts(section_id: int):
    sub = "(SELECT id FROM students WHERE section_id = ?)"
    return {
        "students": fetchone("SELECT COUNT(*) AS c FROM students WHERE section_id = ?", (section_id,))["c"],
        "attendance": fetchone(f"SELECT COUNT(*) AS c FROM attendance WHERE student_id IN {sub}", (section_id,))["c"],
        "exams": fetchone("SELECT COUNT(*) AS c FROM exams WHERE section_id = ?", (section_id,))["c"],
        "links": fetchone(f"SELECT COUNT(*) AS c FROM parent_links WHERE student_id IN {sub}", (section_id,))["c"],
    }


def student_data_counts(student_id: int):
    return {
        "attendance": fetchone("SELECT COUNT(*) AS c FROM attendance WHERE student_id = ?", (student_id,))["c"],
        "scores": fetchone("SELECT COUNT(*) AS c FROM exam_scores WHERE student_id = ?", (student_id,))["c"],
        "links": fetchone("SELECT COUNT(*) AS c FROM parent_links WHERE student_id = ?", (student_id,))["c"],
    }


# ======================================================================
# In-memory state
# ======================================================================

# token -> {"section_id","section_path","date","teacher_id","students","statuses","prev"}
pending_attendance = {}
# admin telegram_id -> {"section_id","path"}   (waiting for an uploaded file)
pending_bulk_upload = {}


# ======================================================================
# Sending helpers
# ======================================================================

def split_text(text: str, limit: int = 3800):
    chunks, cur = [], ""
    for line in text.split("\n"):
        if cur and len(cur) + len(line) + 1 > limit:
            chunks.append(cur.rstrip("\n"))
            cur = ""
        cur += line + "\n"
    if cur.strip():
        chunks.append(cur.rstrip("\n"))
    return chunks or [text]


async def reply_chunks(message, text, reply_markup=None, parse_mode=None):
    chunks = split_text(text)
    for i, c in enumerate(chunks):
        await message.reply_text(
            c, parse_mode=parse_mode,
            reply_markup=reply_markup if i == len(chunks) - 1 else None)


async def safe_send(bot, chat_id, text, **kw) -> bool:
    """Send (in chunks if long); never raises. Returns True on success."""
    try:
        for c in split_text(text):
            await bot.send_message(chat_id=chat_id, text=c, **kw)
        return True
    except Exception as e:
        print(f"[send] failed for chat {chat_id}: {e}")
        return False


def H(text) -> str:
    """HTML-escape user-provided text for parse_mode='HTML' messages."""
    return html.escape(str(text))


# ======================================================================
# Statistics & text builders
# ======================================================================

def student_stats(student_id: int, start_iso: str, end_iso: str) -> dict:
    """Present/late/absent/excused counts and attendance % for a date range.
    Late counts as attended. Excused absences are left out of the percentage."""
    rows = fetchall("""
        SELECT attendance.status,
               (SELECT 1 FROM excuses e WHERE e.student_id = attendance.student_id
                AND e.date = attendance.date) AS excused
        FROM attendance
        WHERE attendance.student_id = ? AND attendance.date >= ? AND attendance.date <= ?
    """, (student_id, start_iso, end_iso))
    present = absent = late = excused = 0
    for r in rows:
        if r["status"] == "present":
            present += 1
        elif r["status"] == "late":
            late += 1
        elif r["status"] == "absent":
            if r["excused"]:
                excused += 1
            else:
                absent += 1
    counted = present + late + absent
    pct = None if counted == 0 else round((present + late) * 100 / counted, 1)
    return {"present": present, "late": late, "absent": absent, "excused": excused, "pct": pct}


def is_low(pct) -> bool:
    return pct is not None and pct < LOW_ATTENDANCE_PCT


def class_tree_text(lang) -> str:
    buildings = fetchall("SELECT * FROM buildings ORDER BY name")
    lines = []
    for b in buildings:
        lines.append(f"🏫 {b['name']}")
        for g in fetchall("SELECT * FROM grades WHERE building_id = ? ORDER BY name", (b["id"],)):
            lines.append(f"  📚 {g['name']}")
            for s in fetchall("SELECT * FROM sections WHERE grade_id = ? ORDER BY name", (g["id"],)):
                count = fetchone("SELECT COUNT(*) AS c FROM students WHERE section_id = ?", (s["id"],))["c"]
                lines.append("    🧑‍🤝‍🧑 " + tr(lang, "tree_section", name=s["name"], n=count))
    return "\n".join(lines) if lines else tr(lang, "no_classes_yet")


def students_list_text(lang, section_id, path) -> str:
    rows = fetchall("""
        SELECT students.id, students.name,
               (SELECT COUNT(*) FROM parent_links WHERE parent_links.student_id = students.id) AS gc
        FROM students WHERE section_id = ? ORDER BY students.name
    """, (section_id,))
    if not rows:
        return tr(lang, "no_students_in", path=path)
    lines = [f"🧑‍🤝‍🧑 {path}:"]
    for s in rows:
        key = "student_linked" if s["gc"] else "student_unlinked"
        lines.append("  • " + tr(lang, key, name=s["name"], n=s["gc"]))
    return "\n".join(lines)


def absentees_text(target_iso: str, lang) -> str:
    rows = fetchall("""
        SELECT students.name AS student_name, attendance.status,
               sections.name AS section_name, grades.name AS grade_name, buildings.name AS building_name,
               (SELECT reason FROM excuses e WHERE e.student_id = attendance.student_id
                AND e.date = attendance.date) AS reason
        FROM attendance
        JOIN students ON attendance.student_id = students.id
        JOIN sections ON students.section_id = sections.id
        JOIN grades ON sections.grade_id = grades.id
        JOIN buildings ON grades.building_id = buildings.id
        WHERE attendance.date = ? AND attendance.status IN ('absent', 'late')
        ORDER BY building_name, grade_name, section_name, student_name
    """, (target_iso,))
    date_s = fmt_date(target_iso, lang)
    if not rows:
        return tr(lang, "absentees_none", date=date_s)
    lines = [tr(lang, "absentees_head", date=date_s)]
    for r in rows:
        line = (f"  {STATUS_EMOJI[r['status']]} {r['student_name']} — "
                f"{r['building_name']} > {r['grade_name']} > {r['section_name']}")
        if r["reason"]:
            line += f"\n      📝 {r['reason']}"
        lines.append(line)
    return "\n".join(lines)


def notification_text(lang, kind, name, path, date_iso, pct=None) -> str:
    text = tr(lang, {"absent": "notify_absent", "late": "notify_late", "back": "notify_back"}[kind],
              name=name, path=path, date=fmt_date(date_iso, lang))
    if kind in ("absent", "late") and is_low(pct):
        text += "\n\n" + tr(lang, "notify_low", name=name, pct=fmt_num(pct), thr=fmt_num(LOW_ATTENDANCE_PCT))
    return text


def monthly_text(section_id: int, lang) -> str:
    path = get_section_path(section_id)
    today = today_iso()
    start, end = eth_month_range(today)
    students = get_students_in_section(section_id)
    head = tr(lang, "monthly_head", path=path, month=eth_month_label(today, lang))
    if not students:
        return head + "\n" + tr(lang, "no_students_short")
    lines = [head, tr(lang, "monthly_legend", thr=fmt_num(LOW_ATTENDANCE_PCT)), ""]
    low_count = 0
    for s in students:
        st = student_stats(s["id"], start, end)
        if st["pct"] is None:
            lines.append(f"• {s['name']} — —")
            continue
        warn = " ⚠️" if is_low(st["pct"]) else ""
        low_count += 1 if warn else 0
        lines.append(f"• {s['name']} — {fmt_num(st['pct'])}% (✅{st['present']} 🕒{st['late']} ❌{st['absent']} 📝{st['excused']}){warn}")
    if low_count:
        lines.append("")
        lines.append(tr(lang, "monthly_low_count", n=low_count))
    return "\n".join(lines)


def weekly_report_text(section_id: int, lang) -> str:
    path = get_section_path(section_id)
    end = today_greg()
    start = end - timedelta(days=6)
    s_iso, e_iso = start.isoformat(), end.isoformat()
    head = tr(lang, "weekly_head", path=path, start=fmt_date(s_iso, lang), end=fmt_date(e_iso, lang))
    students = get_students_in_section(section_id)
    if not students:
        return head + "\n" + tr(lang, "no_students_short")
    days = fetchone("""
        SELECT COUNT(DISTINCT attendance.date) AS c FROM attendance
        JOIN students ON attendance.student_id = students.id
        WHERE students.section_id = ? AND attendance.date >= ? AND attendance.date <= ?
    """, (section_id, s_iso, e_iso))["c"]
    if not days:
        return head + "\n" + tr(lang, "weekly_no_data")
    attended = counted = 0
    lines = []
    for s in students:
        st = student_stats(s["id"], s_iso, e_iso)
        attended += st["present"] + st["late"]
        counted += st["present"] + st["late"] + st["absent"]
        if st["absent"] or st["late"] or st["excused"]:
            warn = " ⚠️" if is_low(st["pct"]) else ""
            lines.append("• " + tr(lang, "weekly_line", name=s["name"], absent=st["absent"], late=st["late"],
                                   excused=st["excused"], pct=fmt_num(st["pct"])) + warn)
    class_pct = round(attended * 100 / counted, 1) if counted else None
    out = [head, tr(lang, "weekly_summary", days=days, pct=fmt_num(class_pct)), ""]
    out += lines if lines else [tr(lang, "weekly_perfect")]
    return "\n".join(out)


# ======================================================================
# Keyboards
# ======================================================================

def build_section_picker(sections, action, extra=None):
    rows = []
    for s in sections:
        cb = f"sec:{action}:{extra}:{s['section_id']}" if extra is not None else f"sec:{action}:{s['section_id']}"
        rows.append([InlineKeyboardButton(
            f"{s['building_name']} > {s['grade_name']} > {s['section_name']}", callback_data=cb)])
    return InlineKeyboardMarkup(rows)


def build_teacher_picker(teachers, action):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(f"{t['name']} ({t['telegram_id']})", callback_data=f"tch:{action}:{t['id']}")]
        for t in teachers])


def build_student_picker(students, action):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(s["name"], callback_data=f"stu:{action}:{s['id']}")] for s in students])


def build_attendance_keyboard(token: str, lang):
    session = pending_attendance[token]
    rows = []
    for student_id, name in session["students"]:
        emoji = STATUS_EMOJI[session["statuses"][student_id]]
        rows.append([InlineKeyboardButton(f"{emoji} {name}", callback_data=f"att:{token}:{student_id}")])
    rows.append([InlineKeyboardButton(tr(lang, "btn_submit_att"), callback_data=f"attsubmit:{token}")])
    return InlineKeyboardMarkup(rows)


# ======================================================================
# Attendance sessions
# ======================================================================

def start_attendance_session(section_id: int, section_path: str, teacher_id: int):
    """Returns (token, editing, error_key). Pre-fills statuses if today's
    attendance was already submitted, so teachers can correct mistakes."""
    students = get_students_in_section(section_id)
    if not students:
        return None, False, "no_students_in"
    today = today_iso()
    existing = {r["student_id"]: r["status"] for r in fetchall("""
        SELECT attendance.student_id, attendance.status FROM attendance
        JOIN students ON attendance.student_id = students.id
        WHERE students.section_id = ? AND attendance.date = ?
    """, (section_id, today))}
    token = secrets.token_hex(4)
    pending_attendance[token] = {
        "section_id": section_id, "section_path": section_path, "date": today,
        "teacher_id": teacher_id,
        "students": [(s["id"], s["name"]) for s in students],
        "statuses": {s["id"]: existing.get(s["id"], "present") for s in students},
        "prev": existing,
    }
    return token, bool(existing), None


async def open_attendance(message, uid, lang, section_id, path):
    token, editing, error = start_attendance_session(section_id, path, uid)
    if error:
        await message.reply_text(tr(lang, error, path=path))
        return
    text = tr(lang, "att_header", path=path, date=fmt_date(pending_attendance[token]["date"], lang))
    if editing:
        text += "\n" + tr(lang, "att_editing")
    await message.reply_text(text, reply_markup=build_attendance_keyboard(token, lang))


async def submit_attendance(context, session: dict):
    """Saves attendance and notifies guardians ONLY about changes:
    new absent/late, or a return to present after a previous absent/late.
    Returns a list of (name, pct) for students below the low-attendance threshold."""
    date_iso = session["date"]
    month_start, month_end = eth_month_range(date_iso)
    stamp = now_eat().isoformat(timespec="seconds")

    conn = db()
    try:
        for student_id, status in session["statuses"].items():
            conn.execute("""
                INSERT INTO attendance (student_id, date, status, marked_by, marked_at)
                VALUES (?, ?, ?, ?, ?)
                ON CONFLICT(student_id, date) DO UPDATE SET status=excluded.status,
                    marked_by=excluded.marked_by, marked_at=excluded.marked_at
            """, (student_id, date_iso, status, session["teacher_id"], stamp))
        conn.commit()
    finally:
        conn.close()

    names = dict(session["students"])
    low_list = []
    for student_id, status in session["statuses"].items():
        prev = session["prev"].get(student_id)
        pct = None
        if status in ("absent", "late"):
            pct = student_stats(student_id, month_start, month_end)["pct"]
            if is_low(pct):
                low_list.append((names[student_id], pct))
        if status == prev:
            continue
        if status == "present":
            if prev not in ("absent", "late"):
                continue
            kind = "back"
        else:
            kind = status
        guardians = fetchall("SELECT chat_id FROM parent_links WHERE student_id = ?", (student_id,))
        for g in guardians:
            text = notification_text(get_lang(g["chat_id"]), kind, names[student_id],
                                     session["section_path"], date_iso, pct)
            await safe_send(context.bot, g["chat_id"], text)
    return low_list


# ======================================================================
# Scheduled jobs (Friday weekly report, weekday reminder)
# ======================================================================

async def send_weekly_reports(bot, only_uid=None):
    """Teachers get their own classes; admins get every class."""
    admin_ids = set(get_admin_ids())
    for t in get_all_teachers():
        uid = t["telegram_id"]
        if uid in admin_ids or (only_uid and uid != only_uid):
            continue
        lang = get_lang(uid)
        for s in fetchall("SELECT section_id FROM teacher_sections WHERE teacher_id = ?", (t["id"],)):
            await safe_send(bot, uid, weekly_report_text(s["section_id"], lang))
    sections = get_all_sections()
    for uid in admin_ids:
        if only_uid and uid != only_uid:
            continue
        lang = get_lang(uid)
        for s in sections:
            await safe_send(bot, uid, weekly_report_text(s["section_id"], lang))


async def job_weekly_report(context: ContextTypes.DEFAULT_TYPE):
    if now_eat().weekday() != 4:  # Friday
        return
    await send_weekly_reports(context.bot)


async def job_attendance_reminder(context: ContextTypes.DEFAULT_TYPE):
    if now_eat().weekday() > 4:  # Saturday/Sunday: no school
        return
    today = today_iso()
    for t in get_all_teachers():
        missing = []
        for s in fetchall("SELECT section_id FROM teacher_sections WHERE teacher_id = ?", (t["id"],)):
            sid = s["section_id"]
            if not get_students_in_section(sid):
                continue
            done = fetchone("""
                SELECT 1 FROM attendance JOIN students ON attendance.student_id = students.id
                WHERE students.section_id = ? AND attendance.date = ? LIMIT 1
            """, (sid, today))
            if not done:
                missing.append(get_section_path(sid))
        if missing:
            lang = get_lang(t["telegram_id"])
            text = tr(lang, "reminder", date=fmt_date(today, lang)) + "\n" + "\n".join(f"  • {p}" for p in missing)
            await safe_send(context.bot, t["telegram_id"], text)


# ======================================================================
# Excel / PDF export (current Ethiopian month)
# ======================================================================

def build_xlsx(section_id: int, lang) -> bytes:
    import openpyxl
    from openpyxl.styles import Font
    path = get_section_path(section_id)
    today = today_iso()
    start, end = eth_month_range(today)
    students = get_students_in_section(section_id)

    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = tr(lang, "xl_attendance")[:31]
    ws.append([f"{path} — {eth_month_label(today, lang)}"])
    ws["A1"].font = Font(bold=True, size=13)
    ws.append([])
    ws.append([tr(lang, "col_student"), tr(lang, "col_present"), tr(lang, "col_absent"),
               tr(lang, "col_late"), tr(lang, "col_excused"), tr(lang, "col_pct")])
    for c in ws[3]:
        c.font = Font(bold=True)
    for s in students:
        st = student_stats(s["id"], start, end)
        ws.append([s["name"], st["present"], st["absent"], st["late"], st["excused"], st["pct"]])
    ws.column_dimensions["A"].width = 32

    exams = fetchall("SELECT id, name, subject, max_score FROM exams WHERE section_id = ? ORDER BY id", (section_id,))
    if exams:
        ws2 = wb.create_sheet(tr(lang, "xl_exams")[:31])
        ws2.append([tr(lang, "col_student")] + [f"{e['subject']} - {e['name']} (/{fmt_num(e['max_score'])})" for e in exams])
        for c in ws2[1]:
            c.font = Font(bold=True)
        for s in students:
            row = [s["name"]]
            for e in exams:
                sc = fetchone("SELECT score FROM exam_scores WHERE exam_id = ? AND student_id = ?", (e["id"], s["id"]))
                row.append(sc["score"] if sc else None)
            ws2.append(row)
        ws2.column_dimensions["A"].width = 32

    bio = io.BytesIO()
    wb.save(bio)
    return bio.getvalue()


def build_pdf(section_id: int, lang) -> bytes:
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer

    font, pdf_lang = "Helvetica", "en"  # Helvetica can't draw Amharic; needs PDF_FONT_PATH
    if PDF_FONT_PATH and os.path.exists(PDF_FONT_PATH):
        pdfmetrics.registerFont(TTFont("EthioFont", PDF_FONT_PATH))
        font, pdf_lang = "EthioFont", lang

    path = get_section_path(section_id)
    today = today_iso()
    start, end = eth_month_range(today)
    title = ParagraphStyle("t", fontName=font, fontSize=14, leading=18)
    data = [[tr(pdf_lang, "col_student"), tr(pdf_lang, "col_present"), tr(pdf_lang, "col_absent"),
             tr(pdf_lang, "col_late"), tr(pdf_lang, "col_excused"), tr(pdf_lang, "col_pct")]]
    for s in get_students_in_section(section_id):
        st = student_stats(s["id"], start, end)
        data.append([s["name"], st["present"], st["absent"], st["late"], st["excused"],
                     "-" if st["pct"] is None else f"{fmt_num(st['pct'])}%"])
    table = Table(data, repeatRows=1)
    table.setStyle(TableStyle([
        ("FONTNAME", (0, 0), (-1, -1), font),
        ("BACKGROUND", (0, 0), (-1, 0), colors.lightgrey),
        ("GRID", (0, 0), (-1, -1), 0.4, colors.grey),
        ("ALIGN", (1, 0), (-1, -1), "CENTER"),
    ]))
    bio = io.BytesIO()
    doc = SimpleDocTemplate(bio, pagesize=A4)
    doc.build([Paragraph(html.escape(f"{path} — {eth_month_label(today, pdf_lang)}"), title), Spacer(1, 12), table])
    return bio.getvalue()


# ======================================================================
# Menu / flow helpers
# ======================================================================

def main_menu(uid: int):
    return menu_for(role_of(uid), get_lang(uid))


def set_flow(context, action, step=0, **data):
    context.user_data["flow"] = {"action": action, "step": step, "data": data}


def clear_flow(context, uid=None):
    context.user_data.pop("flow", None)
    if uid is not None:
        pending_bulk_upload.pop(uid, None)


async def reply_err(message, lang, key, path=""):
    await message.reply_text("❌ " + tr(lang, key, path=path))


def student_code_text(lang, name, code, guardians) -> str:
    status = tr(lang, "linked_n", n=guardians) if guardians else tr(lang, "not_linked")
    return tr(lang, "student_code", name=H(name), code=code, status=status)


async def ask_delete_class(message, lang, section_id):
    path = get_section_path(section_id)
    c = class_data_counts(section_id)
    text = tr(lang, "confirm_del_class", path=path, students=c["students"], attendance=c["attendance"],
              exams=c["exams"], links=c["links"])
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(tr(lang, "btn_yes_delete"), callback_data=f"del:class:{section_id}")],
        [InlineKeyboardButton(tr(lang, "btn_no"), callback_data="del:no")]])
    await message.reply_text(text, reply_markup=kb)


async def ask_delete_student(message, lang, student_id):
    s = fetchone("SELECT name FROM students WHERE id = ?", (student_id,))
    if not s:
        await message.reply_text(tr(lang, "student_gone"))
        return
    c = student_data_counts(student_id)
    text = tr(lang, "confirm_del_student", name=s["name"], attendance=c["attendance"],
              scores=c["scores"], links=c["links"])
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(tr(lang, "btn_yes_delete"), callback_data=f"del:student:{student_id}")],
        [InlineKeyboardButton(tr(lang, "btn_no"), callback_data="del:no")]])
    await message.reply_text(text, reply_markup=kb)


# ======================================================================
# Basic commands
# ======================================================================

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    lang = get_lang(uid)

    if context.args:  # deep link: t.me/<bot>?start=<code>
        await try_link_parent(update, context.args[0])
        return

    if not any_admin_exists():
        execute("INSERT INTO admins (telegram_id) VALUES (?)", (uid,))
        await update.message.reply_text(tr(lang, "welcome_first_admin"), reply_markup=menu_for("admin", lang))
        return

    role = role_of(uid)
    if role != "none":
        await update.message.reply_text(tr(lang, f"welcome_{role}"), reply_markup=menu_for(role, lang))
        return

    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(tr(lang, "btn_request_teacher"), callback_data="treg:req")],
        [InlineKeyboardButton("አማርኛ", callback_data="lang:am"), InlineKeyboardButton("English", callback_data="lang:en")],
    ])
    await update.message.reply_text(tr(lang, "welcome_new"), reply_markup=kb)


async def cmd_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    lang = get_lang(uid)
    role = role_of(uid)
    if role == "none":
        await update.message.reply_text(tr(lang, "menu_none"))
    else:
        await update.message.reply_text(tr(lang, f"menu_{role}"), reply_markup=menu_for(role, lang))


async def cmd_language(update: Update, context: ContextTypes.DEFAULT_TYPE):
    lang = get_lang(update.effective_user.id)
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("አማርኛ", callback_data="lang:am"),
        InlineKeyboardButton("English", callback_data="lang:en")]])
    await update.message.reply_text(tr(lang, "choose_language"), reply_markup=kb)


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    lang = get_lang(uid)
    lines = [tr(lang, "help_general")]
    if is_admin(uid):
        lines.append(tr(lang, "help_admin"))
    await update.message.reply_text("\n\n".join(lines))


def require_admin(func):
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update.effective_user.id):
            await update.message.reply_text(tr(get_lang(update.effective_user.id), "admin_only"))
            return
        await func(update, context)
    return wrapper


# ======================================================================
# Admin slash commands
# ======================================================================

@require_admin
async def cmd_addadmin(update, context):
    lang = get_lang(update.effective_user.id)
    if not context.args or not context.args[0].isdigit():
        await update.message.reply_text("Usage: /addadmin <telegram_id>")
        return
    new_id = int(context.args[0])
    execute("INSERT INTO admins (telegram_id) VALUES (?) ON CONFLICT (telegram_id) DO NOTHING", (new_id,))
    await update.message.reply_text(tr(lang, "admin_added", id=new_id))


@require_admin
async def cmd_addclass(update, context):
    lang = get_lang(update.effective_user.id)
    result, error = get_or_create_class_path(" ".join(context.args))
    if error:
        await reply_err(update.message, lang, error)
        return
    await update.message.reply_text(tr(lang, "class_ready", path=result["path"]))


@require_admin
async def cmd_addclasses(update, context):
    lang = get_lang(update.effective_user.id)
    parsed = parse_path(" ".join(context.args))
    if not parsed:
        await update.message.reply_text("Usage: /addclasses Building > Grade > Section A to H")
        return
    building, grade, section_spec = parsed
    names = parse_section_range(section_spec)
    if not names:
        await update.message.reply_text("❌ " + tr(lang, "err_range"))
        return
    created = []
    for n in names:
        result, error = get_or_create_class_path(f"{building} > {grade} > {n}")
        if not error:
            created.append(result["path"])
    if not created:
        await update.message.reply_text(tr(lang, "no_class_created"))
        return
    await update.message.reply_text(tr(lang, "classes_ready") + "\n" + "\n".join(f"  • {p}" for p in created))


@require_admin
async def cmd_editclass(update, context):
    lang = get_lang(update.effective_user.id)
    full = " ".join(context.args)
    if "|" not in full:
        await update.message.reply_text("Usage: /editclass Old Building > Old Grade > Old Section | New Building > New Grade > New Section")
        return
    old_path, new_path = (p.strip() for p in full.split("|", 1))
    ids, error = find_class_ids(old_path)
    if error:
        await reply_err(update.message, lang, error, old_path)
        return
    parsed = parse_path(new_path)
    if not parsed:
        await reply_err(update.message, lang, "err_format")
        return
    try:
        conn = db()
        conn.execute("UPDATE buildings SET name = ? WHERE id = ?", (parsed[0], ids["building_id"]))
        conn.execute("UPDATE grades SET name = ? WHERE id = ?", (parsed[1], ids["grade_id"]))
        conn.execute("UPDATE sections SET name = ? WHERE id = ?", (parsed[2], ids["section_id"]))
        conn.commit()
        conn.close()
    except Exception as e:
        await update.message.reply_text(tr(lang, "save_failed", err=e))
        return
    await update.message.reply_text(tr(lang, "class_updated", path=" > ".join(parsed)))


@require_admin
async def cmd_editstudent(update, context):
    lang = get_lang(update.effective_user.id)
    parts = [p.strip() for p in " ".join(context.args).split("|")]
    if len(parts) != 3:
        await update.message.reply_text("Usage: /editstudent Building > Grade > Section | Old Name | New Name")
        return
    path_str, old_name, new_name = parts
    result, error = find_class_path(path_str)
    if error:
        await reply_err(update.message, lang, error, path_str)
        return
    s = fetchone("SELECT id FROM students WHERE section_id = ? AND LOWER(name) = LOWER(?)", (result["section_id"], old_name))
    if not s:
        await update.message.reply_text(tr(lang, "student_not_found", name=old_name, path=result["path"]))
        return
    execute("UPDATE students SET name = ? WHERE id = ?", (new_name, s["id"]))
    await update.message.reply_text(tr(lang, "student_renamed", old=old_name, new=new_name))


@require_admin
async def cmd_movestudent(update, context):
    lang = get_lang(update.effective_user.id)
    parts = [p.strip() for p in " ".join(context.args).split("|")]
    if len(parts) != 3:
        await update.message.reply_text("Usage: /movestudent Old Path | Student Name | New Path")
        return
    old_path, name, new_path = parts
    old_r, error = find_class_path(old_path)
    if error:
        await reply_err(update.message, lang, error, old_path)
        return
    new_r, error = find_class_path(new_path)
    if error:
        await reply_err(update.message, lang, error, new_path)
        return
    s = fetchone("SELECT id FROM students WHERE section_id = ? AND LOWER(name) = LOWER(?)", (old_r["section_id"], name))
    if not s:
        await update.message.reply_text(tr(lang, "student_not_found", name=name, path=old_r["path"]))
        return
    execute("UPDATE students SET section_id = ? WHERE id = ?", (new_r["section_id"], s["id"]))
    await update.message.reply_text(tr(lang, "student_moved", name=name, old=old_r["path"], new=new_r["path"]))


@require_admin
async def cmd_addstudent(update, context):
    lang = get_lang(update.effective_user.id)
    full = " ".join(context.args)
    if "|" not in full:
        await update.message.reply_text("Usage: /addstudent Building > Grade > Section | Student Full Name")
        return
    path_str, name = (p.strip() for p in full.split("|", 1))
    if not name:
        await update.message.reply_text(tr(lang, "need_name"))
        return
    result, error = find_class_path(path_str)
    if error:
        await reply_err(update.message, lang, error, path_str)
        return
    code = create_student(result["section_id"], name)
    await update.message.reply_text(
        tr(lang, "student_added", name=H(name), path=H(result["path"]), code=code), parse_mode="HTML")


@require_admin
async def cmd_addstudents(update, context):
    lang = get_lang(update.effective_user.id)
    path_str = " ".join(context.args)
    if not path_str:
        await update.message.reply_text("Usage: /addstudents Building > Grade > Section")
        return
    result, error = find_class_path(path_str)
    if error:
        await reply_err(update.message, lang, error, path_str)
        return
    pending_bulk_upload[update.effective_user.id] = result
    await update.message.reply_text(tr(lang, "upload_ready", path=result["path"]))


@require_admin
async def cmd_addteacher(update, context):
    lang = get_lang(update.effective_user.id)
    if len(context.args) < 2 or not context.args[0].lstrip("@").isdigit():
        await update.message.reply_text("Usage: /addteacher <numeric telegram_id> <Teacher Name>")
        return
    tid = int(context.args[0].lstrip("@"))
    name = " ".join(context.args[1:])
    execute("INSERT INTO teachers (telegram_id, name) VALUES (?, ?) ON CONFLICT (telegram_id) DO NOTHING", (tid, name))
    execute("DELETE FROM pending_teachers WHERE telegram_id = ?", (tid,))
    await update.message.reply_text(tr(lang, "teacher_added", name=name, id=tid))


@require_admin
async def cmd_assignteacher(update, context):
    lang = get_lang(update.effective_user.id)
    if len(context.args) < 2 or not context.args[0].lstrip("@").isdigit():
        await update.message.reply_text("Usage: /assignteacher <numeric telegram_id> <Building > Grade > Section>")
        return
    tid = int(context.args[0].lstrip("@"))
    path_str = " ".join(context.args[1:])
    result, error = find_class_path(path_str)
    if error:
        await reply_err(update.message, lang, error, path_str)
        return
    teacher = fetchone("SELECT id, name FROM teachers WHERE telegram_id = ?", (tid,))
    if not teacher:
        await update.message.reply_text(tr(lang, "teacher_unknown"))
        return
    execute("INSERT INTO teacher_sections (teacher_id, section_id) VALUES (?, ?) "
            "ON CONFLICT (teacher_id, section_id) DO NOTHING", (teacher["id"], result["section_id"]))
    await update.message.reply_text(tr(lang, "teacher_assigned", name=teacher["name"], path=result["path"]))


@require_admin
async def cmd_listclasses(update, context):
    await reply_chunks(update.message, class_tree_text(get_lang(update.effective_user.id)))


@require_admin
async def cmd_liststudents(update, context):
    lang = get_lang(update.effective_user.id)
    path_str = " ".join(context.args)
    result, error = find_class_path(path_str)
    if error:
        await reply_err(update.message, lang, error, path_str)
        return
    await reply_chunks(update.message, students_list_text(lang, result["section_id"], result["path"]))


@require_admin
async def cmd_studentcode(update, context):
    lang = get_lang(update.effective_user.id)
    full = " ".join(context.args)
    if "|" not in full:
        await update.message.reply_text("Usage: /studentcode Building > Grade > Section | Student Name")
        return
    path_str, name = (p.strip() for p in full.split("|", 1))
    result, error = find_class_path(path_str)
    if error:
        await reply_err(update.message, lang, error, path_str)
        return
    s = fetchone("""
        SELECT students.name, students.link_code,
               (SELECT COUNT(*) FROM parent_links WHERE parent_links.student_id = students.id) AS gc
        FROM students WHERE section_id = ? AND LOWER(students.name) LIKE LOWER(?)
    """, (result["section_id"], f"%{name}%"))
    if not s:
        await update.message.reply_text(tr(lang, "student_not_found", name=name, path=result["path"]))
        return
    await update.message.reply_text(student_code_text(lang, s["name"], s["link_code"], s["gc"]), parse_mode="HTML")


@require_admin
async def cmd_absentees(update, context):
    lang = get_lang(update.effective_user.id)
    if context.args:
        iso = parse_eth_date(context.args[0])
        if not iso:
            await update.message.reply_text(tr(lang, "bad_eth_date"))
            return
    else:
        iso = today_iso()
    await reply_chunks(update.message, absentees_text(iso, lang))


@require_admin
async def cmd_removeclass(update, context):
    lang = get_lang(update.effective_user.id)
    path_str = " ".join(context.args)
    result, error = find_class_path(path_str)
    if error:
        await reply_err(update.message, lang, error, path_str)
        return
    await ask_delete_class(update.message, lang, result["section_id"])


@require_admin
async def cmd_removestudent(update, context):
    lang = get_lang(update.effective_user.id)
    full = " ".join(context.args)
    if "|" not in full:
        await update.message.reply_text("Usage: /removestudent Building > Grade > Section | Student Name")
        return
    path_str, name = (p.strip() for p in full.split("|", 1))
    result, error = find_class_path(path_str)
    if error:
        await reply_err(update.message, lang, error, path_str)
        return
    s = fetchone("SELECT id FROM students WHERE section_id = ? AND LOWER(name) = LOWER(?)", (result["section_id"], name))
    if not s:
        await update.message.reply_text(tr(lang, "student_not_found", name=name, path=result["path"]))
        return
    await ask_delete_student(update.message, lang, s["id"])


async def cmd_weekly(update, context):
    uid = update.effective_user.id
    lang = get_lang(uid)
    if role_of(uid) not in ("admin", "teacher"):
        await update.message.reply_text(tr(lang, "not_teacher"))
        return
    await send_weekly_reports(context.bot, only_uid=uid)


# ======================================================================
# Teacher commands + parent linking
# ======================================================================

async def user_class_pick(message, uid, lang, action, prompt_key):
    if role_of(uid) not in ("admin", "teacher"):
        await message.reply_text(tr(lang, "not_teacher"))
        return
    sections = sections_for_user(uid)
    if not sections:
        await message.reply_text(tr(lang, "no_classes_for_you"))
        return
    await message.reply_text(tr(lang, prompt_key), reply_markup=build_section_picker(sections, action))


async def cmd_myclasses(update, context):
    uid = update.effective_user.id
    await user_class_pick(update.message, uid, get_lang(uid), "attendance", "tap_class_attendance")


async def cmd_attendance(update, context):
    uid = update.effective_user.id
    lang = get_lang(uid)
    path_str = " ".join(context.args)
    result, error = find_class_path(path_str)
    if error:
        await reply_err(update.message, lang, error, path_str)
        return
    if role_of(uid) not in ("admin", "teacher"):
        await update.message.reply_text(tr(lang, "not_teacher"))
        return
    if not can_access_section(uid, result["section_id"]):
        await update.message.reply_text(tr(lang, "not_assigned"))
        return
    await open_attendance(update.message, uid, lang, result["section_id"], result["path"])


async def try_link_parent(update: Update, code: str):
    uid = update.effective_user.id
    lang = get_lang(uid)
    chat_id = update.effective_chat.id
    student = fetchone("SELECT id, name FROM students WHERE link_code = ?", (code.strip().upper(),))
    if not student:
        await update.message.reply_text(tr(lang, "link_invalid"))
        return
    if fetchone("SELECT 1 FROM parent_links WHERE student_id = ? AND chat_id = ?", (student["id"], chat_id)):
        await update.message.reply_text(tr(lang, "link_already", name=student["name"]))
        return
    execute("INSERT INTO parent_links (student_id, chat_id) VALUES (?, ?) ON CONFLICT (student_id, chat_id) DO NOTHING",
            (student["id"], chat_id))
    await update.message.reply_text(tr(lang, "link_ok", name=student["name"]), reply_markup=main_menu(uid))


async def cmd_link(update, context):
    if not context.args:
        await update.message.reply_text("Usage: /link <code>")
        return
    await try_link_parent(update, context.args[0])


# ======================================================================
# Bulk student upload (Excel / CSV / PDF)
# ======================================================================

def _extract_names_from_xlsx(file_bytes: bytes):
    import openpyxl
    ws = openpyxl.load_workbook(io.BytesIO(file_bytes), data_only=True).active
    names = []
    for row in ws.iter_rows(values_only=True):
        if row and row[0] is not None:
            name = str(row[0]).strip()
            if name and name.lower() not in NAME_HEADER_WORDS:
                names.append(name)
    return names


def _extract_names_from_csv(file_bytes: bytes):
    names = []
    for row in csv.reader(io.StringIO(file_bytes.decode("utf-8", errors="ignore"))):
        if row:
            name = row[0].strip()
            if name and name.lower() not in NAME_HEADER_WORDS:
                names.append(name)
    return names


def _extract_names_from_pdf(file_bytes: bytes):
    import pdfplumber
    names = []
    with pdfplumber.open(io.BytesIO(file_bytes)) as pdf:
        for page in pdf.pages:
            for line in (page.extract_text() or "").split("\n"):
                line = line.strip()
                if line and line.lower() not in NAME_HEADER_WORDS:
                    names.append(line)
    return names


async def on_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    lang = get_lang(uid)
    pending = pending_bulk_upload.get(uid)
    if not pending:
        return
    document = update.message.document
    filename = document.file_name or ""
    ext = filename.lower().rsplit(".", 1)[-1] if "." in filename else ""
    if ext not in ("xlsx", "csv", "pdf"):
        await update.message.reply_text(tr(lang, "bad_file_type"))
        return

    tg_file = await document.get_file()
    file_bytes = bytes(await tg_file.download_as_bytearray())
    try:
        names = {"xlsx": _extract_names_from_xlsx, "csv": _extract_names_from_csv,
                 "pdf": _extract_names_from_pdf}[ext](file_bytes)
    except Exception as e:
        await update.message.reply_text(tr(lang, "file_read_failed", err=e))
        return
    if not names:
        await update.message.reply_text(tr(lang, "no_names_found"))
        return

    added = [(n, create_student(pending["section_id"], n)) for n in names]
    pending_bulk_upload.pop(uid, None)
    text = tr(lang, "students_added_head", n=len(added), path=H(pending["path"])) + "\n"
    text += "\n".join(f"  • {H(n)} — <code>{c}</code>" for n, c in added)
    await reply_chunks(update.message, text, parse_mode="HTML", reply_markup=main_menu(uid))


# ======================================================================
# Reply-keyboard button handlers
# ======================================================================

async def _admin_class_pick(update, action, prompt_key):
    uid = update.effective_user.id
    lang = get_lang(uid)
    if not is_admin(uid):
        return
    sections = get_all_sections()
    if not sections:
        await update.message.reply_text(tr(lang, "no_classes_admin"), reply_markup=main_menu(uid))
        return
    await update.message.reply_text(tr(lang, prompt_key), reply_markup=build_section_picker(sections, action))


async def btn_add_class(update, context):
    uid = update.effective_user.id
    if not is_admin(uid):
        return
    lang = get_lang(uid)
    set_flow(context, "addclass")
    await update.message.reply_text(tr(lang, "ask_building"), reply_markup=cancel_menu(lang))


async def btn_bulk_classes(update, context):
    uid = update.effective_user.id
    if not is_admin(uid):
        return
    lang = get_lang(uid)
    set_flow(context, "bulkclasses")
    await update.message.reply_text(tr(lang, "ask_building"), reply_markup=cancel_menu(lang))


async def btn_edit_class(update, context):
    await _admin_class_pick(update, "editclass", "which_class_edit")


async def btn_del_class(update, context):
    await _admin_class_pick(update, "delclass", "which_class_remove")


async def btn_add_student(update, context):
    await _admin_class_pick(update, "addstudent", "which_class")


async def btn_bulk_students(update, context):
    await _admin_class_pick(update, "bulkstudents", "which_class")


async def btn_edit_student(update, context):
    await _admin_class_pick(update, "editstudent", "which_class_student")


async def btn_del_student(update, context):
    await _admin_class_pick(update, "delstudent", "which_class_student")


async def btn_list_students(update, context):
    await _admin_class_pick(update, "liststudents", "which_class")


async def btn_student_code(update, context):
    await _admin_class_pick(update, "studentcode", "which_class_student")


async def btn_assign_teacher(update, context):
    uid = update.effective_user.id
    if not is_admin(uid):
        return
    lang = get_lang(uid)
    teachers = get_all_teachers()
    if not teachers:
        await update.message.reply_text(tr(lang, "no_teachers_yet"), reply_markup=main_menu(uid))
        return
    await update.message.reply_text(tr(lang, "which_teacher"), reply_markup=build_teacher_picker(teachers, "assignteacher"))


async def btn_pending_teachers(update, context):
    uid = update.effective_user.id
    if not is_admin(uid):
        return
    lang = get_lang(uid)
    rows = fetchall("SELECT telegram_id, name, username FROM pending_teachers ORDER BY requested_at")
    if not rows:
        await update.message.reply_text(tr(lang, "no_pending"))
        return
    for r in rows:
        await update.message.reply_text(
            tr(lang, "admin_new_request", name=r["name"], username=r["username"] or "—", tid=r["telegram_id"]),
            reply_markup=approval_keyboard(lang, r["telegram_id"]))


async def btn_list_classes(update, context):
    uid = update.effective_user.id
    if is_admin(uid):
        await reply_chunks(update.message, class_tree_text(get_lang(uid)))


async def btn_absentees(update, context):
    uid = update.effective_user.id
    if is_admin(uid):
        await reply_chunks(update.message, absentees_text(today_iso(), get_lang(uid)))


async def btn_add_admin(update, context):
    uid = update.effective_user.id
    if not is_admin(uid):
        return
    lang = get_lang(uid)
    set_flow(context, "addadmin")
    await update.message.reply_text(tr(lang, "ask_admin_id"), reply_markup=cancel_menu(lang))


async def btn_announce(update, context):
    uid = update.effective_user.id
    if not is_admin(uid):
        return
    lang = get_lang(uid)
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(tr(lang, "ann_all_parents"), callback_data="ann:all")],
        [InlineKeyboardButton(tr(lang, "ann_one_class"), callback_data="ann:class")],
        [InlineKeyboardButton(tr(lang, "ann_teachers"), callback_data="ann:teachers")],
    ])
    await update.message.reply_text(tr(lang, "ann_who"), reply_markup=kb)


async def btn_weekly(update, context):
    uid = update.effective_user.id
    await user_class_pick(update.message, uid, get_lang(uid), "weekly", "which_class")


async def btn_monthly(update, context):
    uid = update.effective_user.id
    await user_class_pick(update.message, uid, get_lang(uid), "monthly", "which_class")


async def btn_export(update, context):
    uid = update.effective_user.id
    await user_class_pick(update.message, uid, get_lang(uid), "export", "which_class")


async def btn_my_classes(update, context):
    await cmd_myclasses(update, context)


async def btn_notes(update, context):
    uid = update.effective_user.id
    await user_class_pick(update.message, uid, get_lang(uid), "notes", "which_class")


async def btn_exams(update, context):
    uid = update.effective_user.id
    lang = get_lang(uid)
    if role_of(uid) not in ("admin", "teacher"):
        await update.message.reply_text(tr(lang, "not_teacher"))
        return
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(tr(lang, "btn_new_exam"), callback_data="exm:new")],
        [InlineKeyboardButton(tr(lang, "btn_my_exams"), callback_data="exm:list")],
    ])
    await update.message.reply_text(tr(lang, "exam_menu"), reply_markup=kb)


async def btn_language(update, context):
    await cmd_language(update, context)


async def btn_cancel(update, context):
    uid = update.effective_user.id
    clear_flow(context, uid)
    await update.message.reply_text(tr(get_lang(uid), "cancelled"), reply_markup=main_menu(uid))


async def btn_children(update, context):
    uid = update.effective_user.id
    lang = get_lang(uid)
    kids = fetchall("""
        SELECT students.id, students.name, students.section_id FROM parent_links
        JOIN students ON parent_links.student_id = students.id
        WHERE parent_links.chat_id = ? ORDER BY students.name
    """, (uid,))
    if not kids:
        await update.message.reply_text(tr(lang, "no_children"))
        return
    today = today_iso()
    start, end = eth_month_range(today)
    blocks = []
    for k in kids:
        st = student_stats(k["id"], start, end)
        line = tr(lang, "child_line", name=k["name"], path=get_section_path(k["section_id"]),
                  month=eth_month_label(today, lang), present=st["present"], late=st["late"],
                  absent=st["absent"], excused=st["excused"], pct=fmt_num(st["pct"]))
        if is_low(st["pct"]):
            line += "\n" + tr(lang, "child_low", thr=fmt_num(LOW_ATTENDANCE_PCT))
        blocks.append(line)
    await reply_chunks(update.message, "\n\n".join(blocks))


async def btn_excuse(update, context):
    uid = update.effective_user.id
    lang = get_lang(uid)
    kids = fetchall("""
        SELECT students.id, students.name FROM parent_links
        JOIN students ON parent_links.student_id = students.id
        WHERE parent_links.chat_id = ? ORDER BY students.name
    """, (uid,))
    if not kids:
        await update.message.reply_text(tr(lang, "no_children"))
        return
    await update.message.reply_text(tr(lang, "excuse_which_child"), reply_markup=build_student_picker(kids, "excuse"))


BUTTON_HANDLERS = {
    "add_class": btn_add_class, "bulk_classes": btn_bulk_classes, "edit_class": btn_edit_class,
    "del_class": btn_del_class, "add_student": btn_add_student, "bulk_students": btn_bulk_students,
    "edit_student": btn_edit_student, "del_student": btn_del_student,
    "pending_teachers": btn_pending_teachers, "assign_teacher": btn_assign_teacher,
    "list_classes": btn_list_classes, "list_students": btn_list_students,
    "student_code": btn_student_code, "absentees": btn_absentees, "weekly": btn_weekly,
    "monthly": btn_monthly, "export": btn_export, "announce": btn_announce,
    "add_admin": btn_add_admin, "language": btn_language, "cancel": btn_cancel,
    "my_classes": btn_my_classes, "exams": btn_exams, "notes": btn_notes,
    "p_children": btn_children, "p_excuse": btn_excuse,
}


# ======================================================================
# Free-text router: menu buttons first, then step-by-step flows
# ======================================================================

async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message or not update.message.text:
        return
    uid = update.effective_user.id
    text = update.message.text.strip()

    key = LABEL_TO_KEY.get(text)
    if key:
        if key != "cancel":
            clear_flow(context, uid)  # tapping a menu button abandons any half-finished flow
        await BUTTON_HANDLERS[key](update, context)
        return

    flow = context.user_data.get("flow")
    if flow:
        await handle_flow(update, context, flow, text)


ADMIN_FLOWS = {"addclass", "bulkclasses", "editclass", "editstudent_rename", "addstudent", "addadmin", "announce"}
STAFF_FLOWS = {"examnew", "examscores", "examedit", "examsetmax", "note"}


async def handle_flow(update, context, flow, text):
    uid = update.effective_user.id
    lang = get_lang(uid)
    msg = update.message
    action, step, data = flow["action"], flow["step"], flow["data"]
    cancel_kb = cancel_menu(lang)

    if action in ADMIN_FLOWS and not is_admin(uid):
        clear_flow(context)
        return
    if action in STAFF_FLOWS and role_of(uid) not in ("admin", "teacher"):
        clear_flow(context)
        return
    if action == "excuse" and not is_parent(uid):
        clear_flow(context)
        return

    # ---------------- classes ----------------
    if action == "addclass":
        if step == 0:
            data["building"], flow["step"] = text, 1
            await msg.reply_text(tr(lang, "ask_grade"), reply_markup=cancel_kb)
        elif step == 1:
            data["grade"], flow["step"] = text, 2
            await msg.reply_text(tr(lang, "ask_section"), reply_markup=cancel_kb)
        else:
            result, error = get_or_create_class_path(f"{data['building']} > {data['grade']} > {text}")
            clear_flow(context)
            if error:
                await msg.reply_text("❌ " + tr(lang, error), reply_markup=main_menu(uid))
            else:
                await msg.reply_text(tr(lang, "class_ready", path=result["path"]), reply_markup=main_menu(uid))
        return

    if action == "bulkclasses":
        if step == 0:
            data["building"], flow["step"] = text, 1
            await msg.reply_text(tr(lang, "ask_grade"), reply_markup=cancel_kb)
        elif step == 1:
            data["grade"], flow["step"] = text, 2
            await msg.reply_text(tr(lang, "ask_section_range"), reply_markup=cancel_kb)
        else:
            names = parse_section_range(text) or [text]
            created = []
            for n in names:
                result, error = get_or_create_class_path(f"{data['building']} > {data['grade']} > {n}")
                if not error:
                    created.append(result["path"])
            clear_flow(context)
            if not created:
                await msg.reply_text(tr(lang, "no_class_created"), reply_markup=main_menu(uid))
            else:
                await msg.reply_text(tr(lang, "classes_ready") + "\n" + "\n".join(f"  • {p}" for p in created),
                                     reply_markup=main_menu(uid))
        return

    if action == "editclass":
        if step == 0:
            data["new_building"], flow["step"] = text, 1
            await msg.reply_text(tr(lang, "ask_new_grade", old=data["old_grade"]), reply_markup=cancel_kb)
        elif step == 1:
            data["new_grade"], flow["step"] = text, 2
            await msg.reply_text(tr(lang, "ask_new_section", old=data["old_section"]), reply_markup=cancel_kb)
        else:
            data["new_section"] = text
            try:
                conn = db()
                conn.execute("UPDATE buildings SET name = ? WHERE id = ?", (data["new_building"], data["building_id"]))
                conn.execute("UPDATE grades SET name = ? WHERE id = ?", (data["new_grade"], data["grade_id"]))
                conn.execute("UPDATE sections SET name = ? WHERE id = ?", (data["new_section"], data["section_id"]))
                conn.commit()
                conn.close()
                reply = tr(lang, "class_updated", path=f"{data['new_building']} > {data['new_grade']} > {data['new_section']}")
            except Exception as e:
                reply = tr(lang, "save_failed", err=e)
            clear_flow(context)
            await msg.reply_text(reply, reply_markup=main_menu(uid))
        return

    # ---------------- students ----------------
    if action == "editstudent_rename":
        execute("UPDATE students SET name = ? WHERE id = ?", (text, data["student_id"]))
        clear_flow(context)
        await msg.reply_text(tr(lang, "student_renamed", old=data["old_name"], new=text), reply_markup=main_menu(uid))
        return

    if action == "addstudent":
        code = create_student(data["section_id"], text)
        clear_flow(context)
        await msg.reply_text(tr(lang, "student_added", name=H(text), path=H(data["path"]), code=code),
                             parse_mode="HTML", reply_markup=main_menu(uid))
        return

    # ---------------- admins ----------------
    if action == "addadmin":
        if not text.isdigit():
            await msg.reply_text(tr(lang, "need_numeric_id"), reply_markup=cancel_kb)
            return
        execute("INSERT INTO admins (telegram_id) VALUES (?) ON CONFLICT (telegram_id) DO NOTHING", (int(text),))
        clear_flow(context)
        await msg.reply_text(tr(lang, "admin_added", id=text), reply_markup=main_menu(uid))
        return

    # ---------------- announcements ----------------
    if action == "announce":
        n = await send_announcement(context, data["target"], text, data.get("section_id"))
        clear_flow(context)
        await msg.reply_text(tr(lang, "ann_sent", n=n), reply_markup=main_menu(uid))
        return

    # ---------------- notes to parents ----------------
    if action == "note":
        n = await send_note(context, uid, data, text)
        clear_flow(context)
        await msg.reply_text(tr(lang, "note_sent", n=n), reply_markup=main_menu(uid))
        return

    # ---------------- exams ----------------
    if action == "examnew":
        if step == 0:
            data["name"], flow["step"] = text, 1
            await msg.reply_text(tr(lang, "ask_exam_subject"), reply_markup=cancel_kb)
        elif step == 1:
            data["subject"], flow["step"] = text, 2
            await msg.reply_text(tr(lang, "ask_exam_max"), reply_markup=cancel_kb)
        else:
            mx = parse_number(text)
            if mx is None or mx <= 0:
                await msg.reply_text(tr(lang, "need_positive_number"), reply_markup=cancel_kb)
                return
            students = get_students_in_section(data["section_id"])
            if not students:
                clear_flow(context)
                await msg.reply_text(tr(lang, "no_students_in", path=get_section_path(data["section_id"])),
                                     reply_markup=main_menu(uid))
                return
            execute("INSERT INTO exams (section_id, name, subject, max_score, exam_date, created_by) VALUES (?, ?, ?, ?, ?, ?)",
                    (data["section_id"], data["name"], data["subject"], mx, today_iso(), uid))
            exam_id = fetchone("SELECT id FROM exams WHERE created_by = ? ORDER BY id DESC LIMIT 1", (uid,))["id"]
            set_flow(context, "examscores", exam_id=exam_id, max=mx,
                     queue=[(s["id"], s["name"]) for s in students], idx=0)
            await exam_prompt_score(msg, lang, context.user_data["flow"])
        return

    if action == "examscores":
        v = parse_number(text)
        if v is None or v < 0 or v > data["max"]:
            await msg.reply_text(tr(lang, "score_invalid", max=fmt_num(data["max"])))
            return
        sid, _ = data["queue"][data["idx"]]
        save_score(data["exam_id"], sid, v)
        data["idx"] += 1
        await exam_prompt_score(msg, lang, flow)
        return

    if action == "examedit":
        v = parse_number(text)
        mx = fetchone("SELECT max_score FROM exams WHERE id = ?", (data["exam_id"],))["max_score"]
        if v is None or v < 0 or v > mx:
            await msg.reply_text(tr(lang, "score_invalid", max=fmt_num(mx)), reply_markup=cancel_kb)
            return
        save_score(data["exam_id"], data["student_id"], v)
        clear_flow(context)
        await msg.reply_text(tr(lang, "score_saved"), reply_markup=main_menu(uid))
        await show_exam(msg, lang, data["exam_id"])
        return

    if action == "examsetmax":
        v = parse_number(text)
        top = fetchone("SELECT MAX(score) AS m FROM exam_scores WHERE exam_id = ?", (data["exam_id"],))["m"]
        if v is None or v <= 0:
            await msg.reply_text(tr(lang, "need_positive_number"), reply_markup=cancel_kb)
            return
        if top is not None and v < top:
            await msg.reply_text(tr(lang, "max_too_low", top=fmt_num(top)), reply_markup=cancel_kb)
            return
        execute("UPDATE exams SET max_score = ? WHERE id = ?", (v, data["exam_id"]))
        clear_flow(context)
        await msg.reply_text(tr(lang, "max_updated"), reply_markup=main_menu(uid))
        await show_exam(msg, lang, data["exam_id"])
        return

    # ---------------- parent excuse ----------------
    if action == "excuse":
        sid, iso = data["student_id"], data["date"]
        if not fetchone("SELECT 1 FROM parent_links WHERE student_id = ? AND chat_id = ?", (sid, uid)):
            clear_flow(context)
            return
        execute("""INSERT INTO excuses (student_id, date, reason, chat_id, created_at) VALUES (?, ?, ?, ?, ?)
                   ON CONFLICT (student_id, date) DO UPDATE SET reason = excluded.reason,
                   chat_id = excluded.chat_id, created_at = excluded.created_at""",
                (sid, iso, text, uid, now_eat().isoformat(timespec="seconds")))
        clear_flow(context)
        student = fetchone("SELECT name, section_id FROM students WHERE id = ?", (sid,))
        for t in fetchall("""SELECT teachers.telegram_id FROM teacher_sections
                             JOIN teachers ON teacher_sections.teacher_id = teachers.id
                             WHERE teacher_sections.section_id = ?""", (student["section_id"],)):
            tl = get_lang(t["telegram_id"])
            await safe_send(context.bot, t["telegram_id"],
                            tr(tl, "excuse_to_teacher", name=student["name"], date=fmt_date(iso, tl), reason=text))
        await msg.reply_text(tr(lang, "excuse_saved"), reply_markup=main_menu(uid))
        return


# ======================================================================
# Announcements & notes
# ======================================================================

async def send_announcement(context, target, text, section_id=None) -> int:
    if target == "teachers":
        chats = [t["telegram_id"] for t in get_all_teachers()]
    elif target == "class":
        chats = [r["chat_id"] for r in fetchall(
            "SELECT DISTINCT parent_links.chat_id FROM parent_links JOIN students ON parent_links.student_id = students.id "
            "WHERE students.section_id = ?", (section_id,))]
    else:
        chats = [r["chat_id"] for r in fetchall("SELECT DISTINCT chat_id FROM parent_links")]
    sent = 0
    for cid in chats:
        if await safe_send(context.bot, cid, tr(get_lang(cid), "announce_msg", text=text)):
            sent += 1
    return sent


async def send_note(context, uid, data, text) -> int:
    sid, stid, kind = data["section_id"], data["student_id"], data["kind"]
    sender = sender_name(uid)
    sent = 0
    if stid == 0:
        path = get_section_path(sid)
        chats = [r["chat_id"] for r in fetchall(
            "SELECT DISTINCT parent_links.chat_id FROM parent_links JOIN students ON parent_links.student_id = students.id "
            "WHERE students.section_id = ?", (sid,))]
        for cid in chats:
            if await safe_send(context.bot, cid, tr(get_lang(cid), "note_hw_class", path=path, teacher=sender, text=text)):
                sent += 1
        return sent
    student = fetchone("SELECT name FROM students WHERE id = ?", (stid,))
    key = {"hw": "note_hw", "beh": "note_beh", "good": "note_good"}[kind]
    for g in fetchall("SELECT chat_id FROM parent_links WHERE student_id = ?", (stid,)):
        if await safe_send(context.bot, g["chat_id"], tr(get_lang(g["chat_id"]), key, name=student["name"], teacher=sender, text=text)):
            sent += 1
    return sent


# ======================================================================
# Exams
# ======================================================================

def save_score(exam_id: int, student_id: int, score: float):
    execute("""INSERT INTO exam_scores (exam_id, student_id, score) VALUES (?, ?, ?)
               ON CONFLICT (exam_id, student_id) DO UPDATE SET score = excluded.score""",
            (exam_id, student_id, score))


def exams_for_user(uid: int):
    base = """SELECT exams.id, exams.name, exams.subject, sections.name AS section_name, grades.name AS grade_name
              FROM exams JOIN sections ON exams.section_id = sections.id
              JOIN grades ON sections.grade_id = grades.id"""
    if is_admin(uid):
        return fetchall(base + " ORDER BY exams.id DESC LIMIT 30")
    t = fetchone("SELECT id FROM teachers WHERE telegram_id = ?", (uid,))
    if not t:
        return []
    return fetchall(base + " WHERE exams.section_id IN (SELECT section_id FROM teacher_sections WHERE teacher_id = ?)"
                           " ORDER BY exams.id DESC LIMIT 30", (t["id"],))


def exam_detail(exam_id: int, lang):
    e = fetchone("SELECT id, section_id, name, subject, max_score, exam_date FROM exams WHERE id = ?", (exam_id,))
    if not e:
        return None, None
    scores = {r["student_id"]: r["score"] for r in fetchall(
        "SELECT student_id, score FROM exam_scores WHERE exam_id = ?", (exam_id,))}
    students = get_students_in_section(e["section_id"])
    vals = list(scores.values())
    avg = f"{sum(vals) / len(vals):.1f}" if vals else "—"
    text = tr(lang, "exam_detail", subject=e["subject"], name=e["name"], path=get_section_path(e["section_id"]),
              date=fmt_date(e["exam_date"], lang), max=fmt_num(e["max_score"]), avg=avg,
              entered=len(vals), total=len(students))
    rows = []
    for s in students:
        sc = scores.get(s["id"])
        label = f"{s['name']} — {fmt_num(sc) if sc is not None else '?'}/{fmt_num(e['max_score'])}"
        rows.append([InlineKeyboardButton(label, callback_data=f"exm:edit:{exam_id}:{s['id']}")])
    rows.append([InlineKeyboardButton(tr(lang, "btn_change_max"), callback_data=f"exm:max:{exam_id}")])
    return text, InlineKeyboardMarkup(rows)


async def show_exam(message, lang, exam_id):
    text, kb = exam_detail(exam_id, lang)
    if text is None:
        await message.reply_text(tr(lang, "exam_gone"))
        return
    await message.reply_text(text, reply_markup=kb)


async def exam_prompt_score(message, lang, flow):
    """Asks for the next student's score; when everyone is done, shows the exam."""
    data = flow["data"]
    idx, queue = data["idx"], data["queue"]
    if idx >= len(queue):
        flow["action"] = "done"
        await message.reply_text(tr(lang, "exam_done"), reply_markup=main_menu(message.chat_id))
        await show_exam(message, lang, data["exam_id"])
        return
    _, name = queue[idx]
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton(tr(lang, "btn_skip"), callback_data="exm:skip"),
        InlineKeyboardButton(tr(lang, "btn_finish"), callback_data="exm:finish")]])
    await message.reply_text(
        tr(lang, "exam_ask_score", n=idx + 1, total=len(queue), name=name, max=fmt_num(data["max"])),
        reply_markup=kb)


# ======================================================================
# Callback handlers (inline buttons). Router at the bottom.
# ======================================================================

def approval_keyboard(lang, tid):
    return InlineKeyboardMarkup([[
        InlineKeyboardButton(tr(lang, "btn_approve"), callback_data=f"tapp:ok:{tid}"),
        InlineKeyboardButton(tr(lang, "btn_reject"), callback_data=f"tapp:no:{tid}")]])


async def cb_lang(update, context, query, uid, lang, parts):
    new = parts[1] if parts[1] in ("am", "en") else "am"
    set_lang(uid, new)
    await query.answer()
    await query.message.reply_text(tr(new, "language_set"), reply_markup=main_menu(uid))


async def cb_treg(update, context, query, uid, lang, parts):
    user = update.effective_user
    if is_teacher(uid) or is_admin(uid):
        await query.answer(tr(lang, "teacher_already"), show_alert=True)
        return
    if fetchone("SELECT 1 FROM pending_teachers WHERE telegram_id = ?", (uid,)):
        await query.answer(tr(lang, "teacher_req_already"), show_alert=True)
        return
    username = f"@{user.username}" if user.username else ""
    execute("INSERT INTO pending_teachers (telegram_id, name, username, requested_at) VALUES (?, ?, ?, ?)",
            (uid, user.full_name, username, now_eat().isoformat(timespec="seconds")))
    for aid in get_admin_ids():
        alang = get_lang(aid)
        await safe_send(context.bot, aid,
                        tr(alang, "admin_new_request", name=user.full_name, username=username or "—", tid=uid),
                        reply_markup=approval_keyboard(alang, uid))
    await query.answer()
    await query.message.reply_text(tr(lang, "teacher_req_sent"))


async def cb_tapp(update, context, query, uid, lang, parts):
    if not is_admin(uid):
        await query.answer(tr(lang, "admins_only_alert"), show_alert=True)
        return
    act, tid = parts[1], int(parts[2])
    row = fetchone("SELECT name FROM pending_teachers WHERE telegram_id = ?", (tid,))
    if not row:
        await query.answer(tr(lang, "request_handled"), show_alert=True)
        return
    tlang = get_lang(tid)
    await query.answer()
    if act == "ok":
        execute("INSERT INTO teachers (telegram_id, name) VALUES (?, ?) ON CONFLICT (telegram_id) DO NOTHING",
                (tid, row["name"]))
        execute("DELETE FROM pending_teachers WHERE telegram_id = ?", (tid,))
        await query.edit_message_text(tr(lang, "teacher_approved_admin", name=row["name"], tid=tid))
        await safe_send(context.bot, tid, tr(tlang, "teacher_approved_user"), reply_markup=menu_for("teacher", tlang))
    else:
        execute("DELETE FROM pending_teachers WHERE telegram_id = ?", (tid,))
        await query.edit_message_text(tr(lang, "teacher_rejected_admin", name=row["name"], tid=tid))
        await safe_send(context.bot, tid, tr(tlang, "teacher_rejected_user"))


async def cb_att(update, context, query, uid, lang, parts):
    kind = parts[0]
    if kind == "att":
        token, student_id = parts[1], int(parts[2])
        session = pending_attendance.get(token)
        if not session:
            await query.answer(tr(lang, "att_expired"), show_alert=True)
            return
        cur = session["statuses"][student_id]
        session["statuses"][student_id] = STATUS_CYCLE[(STATUS_CYCLE.index(cur) + 1) % len(STATUS_CYCLE)]
        await query.answer()
        await query.edit_message_reply_markup(reply_markup=build_attendance_keyboard(token, lang))
        return
    # attsubmit
    session = pending_attendance.pop(parts[1], None)
    if not session:
        await query.answer(tr(lang, "att_expired"), show_alert=True)
        return
    await query.answer(tr(lang, "submitting"))
    low = await submit_attendance(context, session)
    summary = "\n".join(f"{STATUS_EMOJI[session['statuses'][sid]]} {name}" for sid, name in session["students"])
    text = tr(lang, "att_submitted", path=session["section_path"], date=fmt_date(session["date"], lang)) + "\n\n" + summary
    if low:
        text += "\n\n" + tr(lang, "att_low_head", thr=fmt_num(LOW_ATTENDANCE_PCT)) + "\n"
        text += "\n".join(f"  ⚠️ {n} — {fmt_num(p)}%" for n, p in low)
    await query.edit_message_text(text)


ADMIN_SEC_ACTIONS = {"editclass", "delclass", "addstudent", "bulkstudents", "editstudent", "delstudent",
                     "liststudents", "studentcode", "assignteacher", "mvto", "annclass"}
STAFF_SEC_ACTIONS = {"attendance", "monthly", "export", "weekly", "notes", "examnew"}


async def cb_sec(update, context, query, uid, lang, parts):
    action = parts[1]
    if action in ADMIN_SEC_ACTIONS and not is_admin(uid):
        await query.answer(tr(lang, "admins_only_alert"), show_alert=True)
        return
    if action in STAFF_SEC_ACTIONS and role_of(uid) not in ("admin", "teacher"):
        await query.answer(tr(lang, "not_teacher"), show_alert=True)
        return
    if action == "mvto":
        move_id, sid = int(parts[2]), int(parts[3])
    else:
        sid = int(parts[2])
    path = get_section_path(sid)
    if not path:
        await query.answer(tr(lang, "class_gone"), show_alert=True)
        return
    if action in STAFF_SEC_ACTIONS and not can_access_section(uid, sid):
        await query.answer(tr(lang, "not_assigned"), show_alert=True)
        return
    await query.answer()
    msg = query.message
    cancel_kb = cancel_menu(lang)

    if action == "attendance":
        await open_attendance(msg, uid, lang, sid, path)

    elif action == "monthly":
        await reply_chunks(msg, monthly_text(sid, lang))

    elif action == "weekly":
        await reply_chunks(msg, weekly_report_text(sid, lang))

    elif action == "export":
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("📗 Excel", callback_data=f"fmt:xlsx:{sid}"),
            InlineKeyboardButton("📕 PDF", callback_data=f"fmt:pdf:{sid}")]])
        await msg.reply_text(tr(lang, "export_choose", path=path), reply_markup=kb)

    elif action == "notes":
        rows = [[InlineKeyboardButton(tr(lang, "note_whole_class"), callback_data=f"nt:who:{sid}:0")]]
        for s in get_students_in_section(sid):
            rows.append([InlineKeyboardButton(s["name"], callback_data=f"nt:who:{sid}:{s['id']}")])
        await msg.reply_text(tr(lang, "note_who", path=path), reply_markup=InlineKeyboardMarkup(rows))

    elif action == "examnew":
        set_flow(context, "examnew", 0, section_id=sid)
        await msg.reply_text(tr(lang, "ask_exam_name", path=path), reply_markup=cancel_kb)

    elif action == "editclass":
        info = get_class_ids_and_names(sid)
        set_flow(context, "editclass", 0, building_id=info["building_id"], grade_id=info["grade_id"], section_id=sid,
                 old_building=info["building_name"], old_grade=info["grade_name"], old_section=info["section_name"])
        await msg.reply_text(tr(lang, "ask_new_building", path=path, old=info["building_name"]), reply_markup=cancel_kb)

    elif action == "delclass":
        await ask_delete_class(msg, lang, sid)

    elif action == "addstudent":
        set_flow(context, "addstudent", 1, section_id=sid, path=path)
        await msg.reply_text(tr(lang, "ask_student_name", path=path), reply_markup=cancel_kb)

    elif action == "bulkstudents":
        pending_bulk_upload[uid] = {"section_id": sid, "path": path}
        await msg.reply_text(tr(lang, "upload_ready", path=path))

    elif action in ("editstudent", "delstudent", "studentcode"):
        students = get_students_in_section(sid)
        if not students:
            await msg.reply_text(tr(lang, "no_students_in", path=path))
            return
        await msg.reply_text(tr(lang, "which_student", path=path), reply_markup=build_student_picker(students, action))

    elif action == "liststudents":
        await reply_chunks(msg, students_list_text(lang, sid, path))

    elif action == "assignteacher":
        flow = context.user_data.get("flow")
        if not flow or flow.get("action") != "assignteacher":
            await msg.reply_text(tr(lang, "session_expired"), reply_markup=main_menu(uid))
            return
        execute("INSERT INTO teacher_sections (teacher_id, section_id) VALUES (?, ?) "
                "ON CONFLICT (teacher_id, section_id) DO NOTHING", (flow["data"]["teacher_id"], sid))
        name = flow["data"]["teacher_name"]
        clear_flow(context)
        await msg.reply_text(tr(lang, "teacher_assigned", name=name, path=path), reply_markup=main_menu(uid))

    elif action == "mvto":
        s = fetchone("SELECT name, section_id FROM students WHERE id = ?", (move_id,))
        if not s:
            await msg.reply_text(tr(lang, "student_gone"), reply_markup=main_menu(uid))
            return
        old_path = get_section_path(s["section_id"])
        execute("UPDATE students SET section_id = ? WHERE id = ?", (sid, move_id))
        await msg.reply_text(tr(lang, "student_moved", name=s["name"], old=old_path, new=path), reply_markup=main_menu(uid))

    elif action == "annclass":
        set_flow(context, "announce", 0, target="class", section_id=sid)
        await msg.reply_text(tr(lang, "ann_ask_text_class", path=path), reply_markup=cancel_kb)


async def cb_tch(update, context, query, uid, lang, parts):
    if not is_admin(uid):
        await query.answer(tr(lang, "admins_only_alert"), show_alert=True)
        return
    await query.answer()
    teacher = fetchone("SELECT name FROM teachers WHERE id = ?", (int(parts[2]),))
    if not teacher:
        await query.message.reply_text(tr(lang, "teacher_gone"), reply_markup=main_menu(uid))
        return
    sections = get_all_sections()
    if not sections:
        await query.message.reply_text(tr(lang, "no_classes_admin"), reply_markup=main_menu(uid))
        return
    set_flow(context, "assignteacher", 1, teacher_id=int(parts[2]), teacher_name=teacher["name"])
    await query.message.reply_text(tr(lang, "which_class_for_teacher", name=teacher["name"]),
                                   reply_markup=build_section_picker(sections, "assignteacher"))


async def cb_stu(update, context, query, uid, lang, parts):
    action, stid = parts[1], int(parts[2])
    msg = query.message

    if action == "excuse":  # parents
        if not fetchone("SELECT 1 FROM parent_links WHERE student_id = ? AND chat_id = ?", (stid, uid)):
            await query.answer()
            return
        await query.answer()
        recent = fetchall("SELECT date, status FROM attendance WHERE student_id = ? AND status IN ('absent', 'late') "
                          "ORDER BY date DESC LIMIT 5", (stid,))
        if not recent:
            await msg.reply_text(tr(lang, "excuse_none"))
            return
        kb = InlineKeyboardMarkup([[InlineKeyboardButton(
            f"{STATUS_EMOJI[r['status']]} {fmt_date(r['date'], lang)}", callback_data=f"exc:{stid}:{r['date']}")] for r in recent])
        await msg.reply_text(tr(lang, "excuse_which_date"), reply_markup=kb)
        return

    if not is_admin(uid):
        await query.answer(tr(lang, "admins_only_alert"), show_alert=True)
        return
    await query.answer()
    student = fetchone("SELECT name, link_code FROM students WHERE id = ?", (stid,))
    if not student:
        await msg.reply_text(tr(lang, "student_gone"), reply_markup=main_menu(uid))
        return

    if action == "studentcode":
        gc = fetchone("SELECT COUNT(*) AS c FROM parent_links WHERE student_id = ?", (stid,))["c"]
        await msg.reply_text(student_code_text(lang, student["name"], student["link_code"], gc),
                             parse_mode="HTML", reply_markup=main_menu(uid))
    elif action == "delstudent":
        await ask_delete_student(msg, lang, stid)
    elif action == "editstudent":
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton(tr(lang, "btn_rename"), callback_data=f"ed:rename:{stid}")],
            [InlineKeyboardButton(tr(lang, "btn_move"), callback_data=f"ed:move:{stid}")]])
        await msg.reply_text(tr(lang, "student_what_do", name=student["name"]), reply_markup=kb)


async def cb_ed(update, context, query, uid, lang, parts):
    if not is_admin(uid):
        await query.answer(tr(lang, "admins_only_alert"), show_alert=True)
        return
    act, stid = parts[1], int(parts[2])
    await query.answer()
    student = fetchone("SELECT name FROM students WHERE id = ?", (stid,))
    if not student:
        await query.message.reply_text(tr(lang, "student_gone"), reply_markup=main_menu(uid))
        return
    if act == "rename":
        set_flow(context, "editstudent_rename", 0, student_id=stid, old_name=student["name"])
        await query.message.reply_text(tr(lang, "ask_new_student_name", name=student["name"]), reply_markup=cancel_menu(lang))
    else:
        sections = get_all_sections()
        await query.message.reply_text(tr(lang, "move_to_which", name=student["name"]),
                                       reply_markup=build_section_picker(sections, "mvto", extra=stid))


async def cb_del(update, context, query, uid, lang, parts):
    if not is_admin(uid):
        await query.answer(tr(lang, "admins_only_alert"), show_alert=True)
        return
    await query.answer()
    if parts[1] == "no":
        await query.edit_message_text(tr(lang, "cancelled"))
    elif parts[1] == "class":
        sid = int(parts[2])
        path = get_section_path(sid)
        if not path:
            await query.edit_message_text(tr(lang, "class_gone"))
            return
        delete_class(sid)
        await query.edit_message_text(tr(lang, "class_removed", path=path))
    elif parts[1] == "student":
        stid = int(parts[2])
        s = fetchone("SELECT name FROM students WHERE id = ?", (stid,))
        if not s:
            await query.edit_message_text(tr(lang, "student_gone"))
            return
        delete_student(stid)
        await query.edit_message_text(tr(lang, "student_removed", name=s["name"]))


async def cb_fmt(update, context, query, uid, lang, parts):
    fmt, sid = parts[1], int(parts[2])
    if role_of(uid) not in ("admin", "teacher") or not can_access_section(uid, sid):
        await query.answer(tr(lang, "not_assigned"), show_alert=True)
        return
    await query.answer(tr(lang, "preparing"))
    path = get_section_path(sid)
    if not path:
        await query.message.reply_text(tr(lang, "class_gone"))
        return
    try:
        data = build_xlsx(sid, lang) if fmt == "xlsx" else build_pdf(sid, lang)
    except Exception as e:
        await query.message.reply_text(tr(lang, "export_failed", err=e))
        return
    safe = re.sub(r"[^\w\-]+", "_", path, flags=re.UNICODE).strip("_") or "class"
    await query.message.reply_document(document=io.BytesIO(data), filename=f"{safe}_{today_iso()}.{fmt}")


async def cb_nt(update, context, query, uid, lang, parts):
    if role_of(uid) not in ("admin", "teacher"):
        await query.answer(tr(lang, "not_teacher"), show_alert=True)
        return
    sid, stid = int(parts[2]), int(parts[3])
    if not can_access_section(uid, sid):
        await query.answer(tr(lang, "not_assigned"), show_alert=True)
        return
    await query.answer()
    msg = query.message
    if parts[1] == "who":
        if stid == 0:
            set_flow(context, "note", 0, section_id=sid, student_id=0, kind="hw")
            await msg.reply_text(tr(lang, "note_ask_hw_class"), reply_markup=cancel_menu(lang))
            return
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton(tr(lang, "kind_hw"), callback_data=f"nt:kind:{sid}:{stid}:hw")],
            [InlineKeyboardButton(tr(lang, "kind_beh"), callback_data=f"nt:kind:{sid}:{stid}:beh")],
            [InlineKeyboardButton(tr(lang, "kind_good"), callback_data=f"nt:kind:{sid}:{stid}:good")]])
        await msg.reply_text(tr(lang, "note_kind"), reply_markup=kb)
    else:
        kind = parts[4] if len(parts) > 4 and parts[4] in ("hw", "beh", "good") else "hw"
        set_flow(context, "note", 0, section_id=sid, student_id=stid, kind=kind)
        await msg.reply_text(tr(lang, "note_ask_text"), reply_markup=cancel_menu(lang))


async def cb_ann(update, context, query, uid, lang, parts):
    if not is_admin(uid):
        await query.answer(tr(lang, "admins_only_alert"), show_alert=True)
        return
    await query.answer()
    if parts[1] == "class":
        sections = get_all_sections()
        if not sections:
            await query.message.reply_text(tr(lang, "no_classes_admin"))
            return
        await query.message.reply_text(tr(lang, "which_class"), reply_markup=build_section_picker(sections, "annclass"))
        return
    set_flow(context, "announce", 0, target=parts[1])
    await query.message.reply_text(tr(lang, "ann_ask_text"), reply_markup=cancel_menu(lang))


async def cb_exc(update, context, query, uid, lang, parts):
    stid, iso = int(parts[1]), parts[2]
    if not fetchone("SELECT 1 FROM parent_links WHERE student_id = ? AND chat_id = ?", (stid, uid)):
        await query.answer()
        return
    await query.answer()
    set_flow(context, "excuse", 0, student_id=stid, date=iso)
    await query.message.reply_text(tr(lang, "excuse_ask_reason", date=fmt_date(iso, lang)), reply_markup=cancel_menu(lang))


async def cb_exm(update, context, query, uid, lang, parts):
    if role_of(uid) not in ("admin", "teacher"):
        await query.answer(tr(lang, "not_teacher"), show_alert=True)
        return
    act = parts[1]
    msg = query.message

    if act == "new":
        await query.answer()
        sections = sections_for_user(uid)
        if not sections:
            await msg.reply_text(tr(lang, "no_classes_for_you"))
            return
        await msg.reply_text(tr(lang, "which_class"), reply_markup=build_section_picker(sections, "examnew"))
        return

    if act == "list":
        await query.answer()
        exams = exams_for_user(uid)
        if not exams:
            await msg.reply_text(tr(lang, "no_exams"))
            return
        kb = InlineKeyboardMarkup([[InlineKeyboardButton(
            f"{e['subject']} — {e['name']} ({e['grade_name']} {e['section_name']})"[:60],
            callback_data=f"exm:open:{e['id']}")] for e in exams])
        await msg.reply_text(tr(lang, "pick_exam"), reply_markup=kb)
        return

    if act in ("skip", "finish"):
        flow = context.user_data.get("flow")
        if not flow or flow.get("action") != "examscores":
            await query.answer(tr(lang, "session_expired"), show_alert=True)
            return
        await query.answer()
        if act == "skip":
            flow["data"]["idx"] += 1
            await exam_prompt_score(msg, lang, flow)
        else:
            exam_id = flow["data"]["exam_id"]
            clear_flow(context)
            await msg.reply_text(tr(lang, "exam_done"), reply_markup=main_menu(uid))
            await show_exam(msg, lang, exam_id)
        return

    # open / edit / max all need an exam the user may access
    exam_id = int(parts[2])
    exam = fetchone("SELECT section_id FROM exams WHERE id = ?", (exam_id,))
    if not exam:
        await query.answer(tr(lang, "exam_gone"), show_alert=True)
        return
    if not can_access_section(uid, exam["section_id"]):
        await query.answer(tr(lang, "not_assigned"), show_alert=True)
        return
    await query.answer()
    if act == "open":
        await show_exam(msg, lang, exam_id)
    elif act == "edit":
        stid = int(parts[3])
        s = fetchone("SELECT name FROM students WHERE id = ?", (stid,))
        if not s:
            await msg.reply_text(tr(lang, "student_gone"))
            return
        e = fetchone("SELECT max_score FROM exams WHERE id = ?", (exam_id,))
        set_flow(context, "examedit", 0, exam_id=exam_id, student_id=stid)
        await msg.reply_text(tr(lang, "exam_edit_ask", name=s["name"], max=fmt_num(e["max_score"])),
                             reply_markup=cancel_menu(lang))
    elif act == "max":
        set_flow(context, "examsetmax", 0, exam_id=exam_id)
        await msg.reply_text(tr(lang, "ask_exam_max"), reply_markup=cancel_menu(lang))


CB_HANDLERS = {
    "lang": cb_lang, "treg": cb_treg, "tapp": cb_tapp, "att": cb_att, "attsubmit": cb_att,
    "sec": cb_sec, "tch": cb_tch, "stu": cb_stu, "ed": cb_ed, "del": cb_del, "fmt": cb_fmt,
    "nt": cb_nt, "ann": cb_ann, "exc": cb_exc, "exm": cb_exm,
}


async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    uid = update.effective_user.id
    parts = (query.data or "").split(":")
    handler = CB_HANDLERS.get(parts[0])
    if not handler:
        await query.answer()
        return
    await handler(update, context, query, uid, get_lang(uid), parts)


async def on_error(update, context: ContextTypes.DEFAULT_TYPE):
    print(f"[error] {context.error!r}")
    try:
        if isinstance(update, Update) and update.effective_chat:
            await context.bot.send_message(update.effective_chat.id, tr(get_lang(update.effective_chat.id), "generic_error"))
    except Exception:
        pass


# ======================================================================
# Main
# ======================================================================

def main():
    init_db()
    threading.Thread(target=start_ping_server, daemon=True).start()

    app = Application.builder().token(BOT_TOKEN).build()

    commands = {
        "start": cmd_start, "menu": cmd_menu, "help": cmd_help, "language": cmd_language,
        "addadmin": cmd_addadmin, "addclass": cmd_addclass, "addclasses": cmd_addclasses,
        "editclass": cmd_editclass, "editstudent": cmd_editstudent, "movestudent": cmd_movestudent,
        "addstudent": cmd_addstudent, "addstudents": cmd_addstudents, "addteacher": cmd_addteacher,
        "assignteacher": cmd_assignteacher, "listclasses": cmd_listclasses, "liststudents": cmd_liststudents,
        "studentcode": cmd_studentcode, "absentees": cmd_absentees, "removeclass": cmd_removeclass,
        "removestudent": cmd_removestudent, "weekly": cmd_weekly, "myclasses": cmd_myclasses,
        "attendance": cmd_attendance, "link": cmd_link,
    }
    for name, fn in commands.items():
        app.add_handler(CommandHandler(name, fn))

    app.add_handler(CallbackQueryHandler(on_callback))
    app.add_handler(MessageHandler(filters.Document.ALL, on_document))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.add_error_handler(on_error)

    if app.job_queue is None:
        print("[jobs] JobQueue missing -- install 'python-telegram-bot[job-queue]' for Friday reports & reminders.")
    else:
        app.job_queue.run_daily(job_weekly_report, time=parse_hhmm(os.environ.get("WEEKLY_REPORT_TIME"), "16:00"),
                                name="weekly_report")
        app.job_queue.run_daily(job_attendance_reminder, time=parse_hhmm(os.environ.get("REMINDER_TIME"), "09:30"),
                                name="attendance_reminder")

    print("School attendance bot running.")
    app.run_polling()


if __name__ == "__main__":
    main()
