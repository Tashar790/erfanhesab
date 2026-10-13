# -*- coding: utf-8 -*-
"""عرفان حساب — سیستم جامع حقوق و دستمزد
سازگار با Flet 0.28.x تا 1.0 | توسعه‌دهنده: عرفان بلوچ
"""
import os, sys, csv, glob, re, shutil, sqlite3, hashlib, hmac, secrets
import subprocess, traceback, inspect, tempfile, base64, io
import socket, threading, mimetypes, urllib.parse, http.server, http.client, time, asyncio
from contextlib import contextmanager
from datetime import datetime
from decimal import Decimal, ROUND_HALF_UP
import flet as ft

try:
    import arabic_reshaper as _reshaper
except Exception:
    _reshaper = None
try:
    try:
        from bidi import get_display as _get_display
    except ImportError:
        from bidi.algorithm import get_display as _get_display
except Exception:
    _get_display = None
try:
    from PIL import Image
except Exception:
    Image = None

HERE = os.path.dirname(os.path.abspath(__file__))
# ═══════════════════════ ابزارهای تاریخ شمسی (خودکفا) ═══════════════════════
def g2j(gy, gm, gd):
    """تبدیل میلادی → شمسی."""
    g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    if gy > 1600:
        jy = 979
        gy -= 1600
    else:
        jy = 0
        gy -= 621
    gy2 = gy + 1 if gm > 2 else gy
    days = (365 * gy + (gy2 + 3) // 4 - (gy2 + 99) // 100
            + (gy2 + 399) // 400 - 80 + gd + g_d_m[gm - 1])
    jy += 33 * (days // 12053)
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm = 1 + days // 31
        jd = 1 + days % 31
    else:
        jm = 7 + (days - 186) // 30
        jd = 1 + (days - 186) % 30
    return jy, jm, jd


def j2g(jy, jm, jd):
    """تبدیل شمسی → میلادی (معکوس g2j)."""
    jy += 1595
    days = (-355668 + (365 * jy) + ((jy // 33) * 8)
            + (((jy % 33) + 3) // 4) + jd)
    if jm < 7:
        days += (jm - 1) * 31
    else:
        days += ((jm - 7) * 30) + 186
    gy = 400 * (days // 146097)
    days %= 146097
    if days > 36524:
        days -= 1
        gy += 100 * (days // 36524)
        days %= 36524
        if days >= 365:
            days += 1
    gy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        gy += (days - 1) // 365
        days = (days - 1) % 365
    gd = days + 1
    leap = (gy % 4 == 0 and gy % 100 != 0) or (gy % 400 == 0)
    sal_a = [0, 31, 29 if leap else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    gm = 0
    while gm < 13 and gd > sal_a[gm]:
        gd -= sal_a[gm]
        gm += 1
    return gy, gm, gd


def jalali_weekday(jy, jm, jd):
    """روز هفته شمسی: ۰ = شنبه، ۱ = یک‌شنبه، ... ۶ = جمعه."""
    gy, gm, gd = j2g(jy, jm, jd)
    return (datetime(gy, gm, gd).weekday() + 2) % 7

def jalali_leap(y):
    return (y % 33) in (1, 5, 9, 13, 17, 22, 26, 30)


def days_in_month(year, month):
    if 1 <= month <= 6:
        return 31
    if 7 <= month <= 11:
        return 30
    return 30 if jalali_leap(year) else 29


def days_in_year(year):
    return sum(days_in_month(year, m) for m in range(1, 13))


def jalali_today_str():
    y, m, d = today_jalali()
    return f"{y}/{m:02d}/{d:02d}"


def validate_jalali(s):
    s = norm(s).replace('-', '/')
    parts = s.split('/')
    if len(parts) != 3:
        return False, "قالب تاریخ: 1405/01/01"
    try:
        y, m, d = int(parts[0]), int(parts[1]), int(parts[2])
    except ValueError:
        return False, "تاریخ باید عدد باشد"
    if not (1300 <= y <= 1500):
        return False, "سال 1300 تا 1500"
    if not (1 <= m <= 12):
        return False, "ماه ۱ تا ۱۲"
    if not (1 <= d <= days_in_month(y, m)):
        return False, f"روز ۱ تا {days_in_month(y, m)}"
    return True, ""



APP_TITLE = "عرفان حساب"
# شماره نسخه عمداً در رابط کاربری نمایش داده نمی‌شود.
DEVELOPER = "عرفان بلوچ"
DEVELOPER_PHONE = "09029912252"
MONTHS = ['فروردین','اردیبهشت','خرداد','تیر','مرداد','شهریور',
          'مهر','آبان','آذر','دی','بهمن','اسفند']

STD = {
    'year': 1405, 'min_daily_wage': 5_541_850, 'housing': 30_000_000,
    'food': 22_000_000, 'marriage': 5_000_000, 'child_allowance': 16_625_550,
    'tax_brackets': [
        (0, 400_000_000, 0), (400_000_000, 800_000_000, 10),
        (800_000_000, 1_000_000_000, 15), (1_000_000_000, 1_200_000_000, 20),
        (1_200_000_000, 1_400_000_000, 25), (1_400_000_000, None, 30),
    ],
    'base_year_daily': 166_667, 'hours_per_day': 7.33, 'hours_per_month': 220,
}

_DIG = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")

# ═══════════════════════ لایه سازگاری Flet ═══════════════════════
def _params(cls):
    try: return inspect.signature(cls).parameters
    except (TypeError, ValueError): return {}

def K(cls, *a, **kw):
    ps = _params(cls)
    if not ps or any(p.kind == p.VAR_KEYWORD for p in ps.values()):
        return cls(*a, **kw)
    return cls(*a, **{k: v for k, v in kw.items() if k in ps})

def pad_sym(h=0, v=0):
    P = getattr(ft, "Padding", None)
    if P is not None and hasattr(P, "symmetric"):
        return P.symmetric(horizontal=h, vertical=v)
    return ft.padding.symmetric(horizontal=h, vertical=v)

def pad_only(left=0, top=0, right=0, bottom=0, **kw):
    if 'l' in kw: left = kw['l']
    if 't' in kw: top = kw['t']
    if 'r' in kw: right = kw['r']
    if 'b' in kw: bottom = kw['b']
    P = getattr(ft, "Padding", None)
    if P is not None and hasattr(P, "only"):
        return P.only(left=left, top=top, right=right, bottom=bottom)
    return ft.padding.only(left=left, top=top, right=right, bottom=bottom)

def border_all(w=1, c="#000000"):
    B = getattr(ft, "Border", None)
    if B is not None and hasattr(B, "all"): return B.all(w, c)
    return ft.border.all(w, c)

def alpha(color, a=0x22):
    c = (color or "#000000").lstrip("#")
    if len(c) == 8: c = c[2:]
    return f"#{a:02x}{c}"

def center(): return ft.Alignment(0, 0)

_ICONS = getattr(ft, "Icons", None) or getattr(ft, "icons", None)
def _ic(name, fallback=None):
    for n in (name, fallback, "CIRCLE"):
        if n and _ICONS is not None and hasattr(_ICONS, n):
            return getattr(_ICONS, n)
    return None

def _border_kwargs(radius=12):
    # نسخه‌های جدید Flet: OutlineInputBorder توصیه می‌شود
    out = {}
    try:
        if hasattr(ft, 'OutlineInputBorder'):
            out['border'] = ft.OutlineInputBorder(border_radius=radius)
            return out
    except Exception:
        pass
    # نسخه‌های قدیمی
    if hasattr(ft, "InputBorder"):
        try:
            out["border"] = ft.InputBorder.OUTLINE
        except Exception:
            pass
    out["border_radius"] = radius
    return out

def _safe_ft_run(main_fn):
    r = getattr(ft, "run", None)
    if callable(r): r(main_fn)
    else: ft.app(target=main_fn)

# ═══════════════════════ تم حرفه‌ای ═══════════════════════
THEMES = {
    'navy': {'name': 'نیلی سلطنتی', 'primary': '#1e3a5f', 'primary_dark': '#0f2440',
             'accent': '#f0b429', 'accent_dark': '#c98a1a', 'success': '#10b981',
             'danger': '#ef4444', 'info': '#3b82f6', 'warning': '#f59e0b',
             'purple': '#8b5cf6', 'bg': '#eef2f7', 'bg_dark': '#0a1628',
             'card': '#ffffff', 'card_dark': '#132038', 'text': '#0f172a',
             'text_dark': '#e2e8f0', 'muted': '#64748b', 'muted_dark': '#94a3b8',
             'line': '#e2e8f0', 'line_dark': '#1e3a5f', 'grad': ['#1e3a5f', '#2d5a8c']},
    'emerald': {'name': 'زمرد بهاری', 'primary': '#065f46', 'primary_dark': '#043d2e',
                'accent': '#fbbf24', 'accent_dark': '#d97706', 'success': '#10b981',
                'danger': '#ef4444', 'info': '#06b6d4', 'warning': '#f59e0b',
                'purple': '#8b5cf6', 'bg': '#f0fdf4', 'bg_dark': '#071a13',
                'card': '#ffffff', 'card_dark': '#0d281e', 'text': '#064e3b',
                'text_dark': '#d1fae5', 'muted': '#6b7280', 'muted_dark': '#9ca3af',
                'line': '#d1fae5', 'line_dark': '#134e3a', 'grad': ['#065f46', '#047857']},
    'royal': {'name': 'بنفش شاهانه', 'primary': '#5b21b6', 'primary_dark': '#3f1489',
              'accent': '#f59e0b', 'accent_dark': '#d97706', 'success': '#10b981',
              'danger': '#ef4444', 'info': '#06b6d4', 'warning': '#f59e0b',
              'purple': '#a78bfa', 'bg': '#faf5ff', 'bg_dark': '#0d0620',
              'card': '#ffffff', 'card_dark': '#1a0d3a', 'text': '#4c1d95',
              'text_dark': '#e9d5ff', 'muted': '#6b7280', 'muted_dark': '#a78bfa',
              'line': '#e9d5ff', 'line_dark': '#2e1065', 'grad': ['#5b21b6', '#7c3aed']},
    'sunset': {'name': 'غروب طلایی', 'primary': '#9a3412', 'primary_dark': '#7c2d12',
               'accent': '#fbbf24', 'accent_dark': '#d97706', 'success': '#10b981',
               'danger': '#dc2626', 'info': '#0ea5e9', 'warning': '#f59e0b',
               'purple': '#a855f7', 'bg': '#fff7ed', 'bg_dark': '#1c0e06',
               'card': '#ffffff', 'card_dark': '#2d1810', 'text': '#7c2d12',
               'text_dark': '#fed7aa', 'muted': '#78716c', 'muted_dark': '#a8a29e',
               'line': '#fed7aa', 'line_dark': '#4a2618', 'grad': ['#9a3412', '#c2410c']},
    'slate': {'name': 'خاکستری مدرن', 'primary': '#334155', 'primary_dark': '#1e293b',
              'accent': '#22d3ee', 'accent_dark': '#0891b2', 'success': '#10b981',
              'danger': '#ef4444', 'info': '#3b82f6', 'warning': '#f59e0b',
              'purple': '#8b5cf6', 'bg': '#f8fafc', 'bg_dark': '#0b1220',
              'card': '#ffffff', 'card_dark': '#1e293b', 'text': '#0f172a',
              'text_dark': '#e2e8f0', 'muted': '#64748b', 'muted_dark': '#94a3b8',
              'line': '#e2e8f0', 'line_dark': '#334155', 'grad': ['#334155', '#475569']},
}
STATE = {'theme': 'navy', 'dark': False}

def T():
    th = THEMES[STATE['theme']]; d = STATE['dark']
    return {'name': th['name'], 'primary': th['primary'],
            'primary_dark': th['primary_dark'], 'accent': th['accent'],
            'accent_dark': th['accent_dark'], 'success': th['success'],
            'danger': th['danger'], 'info': th['info'], 'warning': th['warning'],
            'purple': th['purple'], 'bg': th['bg_dark'] if d else th['bg'],
            'card': th['card_dark'] if d else th['card'],
            'text': th['text_dark'] if d else th['text'],
            'muted': th['muted_dark'] if d else th['muted'],
            'line': th['line_dark'] if d else th['line'], 'grad': th['grad']}

# ═══════════════════════ ابزار عمومی ═══════════════════════
def norm(s):
    return (str("" if s is None else s).translate(_DIG)
            .replace("٬", "").replace(",", "").replace("٫", ".").strip())

def parse_int(s):
    keep = ''.join(c for c in norm(s) if c.isdigit() or c == '.')
    if not keep or keep == '.': return 0
    try: return int(round(float(keep)))
    except ValueError: return 0

def parse_float(s):
    keep = ''.join(c for c in norm(s) if c.isdigit() or c in '.-')
    try: return float(keep)
    except ValueError: return 0.0

def to_int_or_none(v):
    """تبدیل ایمن مقدار به int یا None (برای فیلدهای اختیاری)."""
    if v is None: return None
    s = str(v).strip()
    if not s or s in ('—', '-', '--'): return None
    try: return int(float(s))
    except (ValueError, TypeError): return None

def rnd(v):
    if v is None: return 0
    return int(Decimal(str(v)).quantize(Decimal('1'), rounding=ROUND_HALF_UP))

def fmt(n):
    try: return f"{int(round(float(n))):,}"
    except (TypeError, ValueError): return "0"

def hours_to_hm(hours):
    if not hours: return "0:00"
    h = int(hours); m = int(round((hours - h) * 60))
    if m == 60: h += 1; m = 0
    return f"{h}:{m:02d}"



def today_jalali():
    n = datetime.now()
    return g2j(n.year, n.month, n.day)

def jalali_leap(y): return (y % 33) in (1, 5, 9, 13, 17, 22, 26, 30)

def days_in_month(year, month):
    if 1 <= month <= 6: return 31
    if 7 <= month <= 11: return 30
    return 30 if jalali_leap(year) else 29

def days_in_year(year):
    return sum(days_in_month(year, month) for month in range(1, 13))

def jalali_today_str():
    y, m, d = today_jalali()
    return f"{y}/{m:02d}/{d:02d}"

def validate_jalali(s):
    s = norm(s).replace('-', '/')
    parts = s.split('/')
    if len(parts) != 3: return False, "قالب تاریخ: 1405/01/01"
    try:
        y, m, d = int(parts[0]), int(parts[1]), int(parts[2])
    except ValueError: return False, "تاریخ باید عدد باشد"
    if not (1300 <= y <= 1500): return False, "سال 1300 تا 1500"
    if not (1 <= m <= 12): return False, "ماه ۱ تا ۱۲"
    if not (1 <= d <= days_in_month(y, m)): return False, f"روز ۱ تا {days_in_month(y,m)}"
    return True, ""

def get_data_dir():
    # اندروید: از مسیر مخصوص Flet استفاده کن
    if _is_android():
        p = os.environ.get("FLET_APP_STORAGE_DATA")
        if p:
            try:
                os.makedirs(p, exist_ok=True)
                return p
            except Exception:
                pass
        # fallback اندروید
        p = "/data/data/com.flet.app/files"
        try:
            os.makedirs(p, exist_ok=True)
            return p
        except Exception:
            pass

    # دسکتاپ
    cands = [
        os.environ.get("FLET_APP_STORAGE_DATA"),
        os.path.join(os.path.expanduser("~"), ".erfanhesab"),
        os.path.join(tempfile.gettempdir(), "erfanhesab"),
    ]
    for p in cands:
        if not p: continue
        try:
            os.makedirs(p, exist_ok=True)
            probe = os.path.join(p, ".probe")
            with open(probe, "w") as f: f.write("1")
            os.remove(probe)
            return p
        except Exception:
            continue
    return HERE

def log_error(text):
    try:
        with open(os.path.join(get_data_dir(), "error.log"), "a", encoding="utf-8") as f:
            f.write(f"\n[{datetime.now():%Y-%m-%d %H:%M:%S}]\n{text}\n")
    except Exception: pass

def _writable(d):
    try:
        os.makedirs(d, exist_ok=True)
        p = os.path.join(d, ".w")
        with open(p, "w") as f: f.write("1")
        os.remove(p)
        return True
    except Exception: return False

def export_dir():
    if _is_android():
        # اندروید: پوشه‌ی اپ
        d = os.path.join(get_data_dir(), "exports")
        os.makedirs(d, exist_ok=True)
        return d

    # دسکتاپ
    for base in ("/storage/emulated/0/Download", "/sdcard/Download",
                 os.path.join(os.path.expanduser("~"), "Downloads")):
        if os.path.isdir(base):
            d = os.path.join(base, "ErfanHesab")
            if _writable(d): return d
    d = os.path.join(get_data_dir(), "exports")
    os.makedirs(d, exist_ok=True)
    return d

def hash_pw(pw, salt=None):
    salt = salt or secrets.token_hex(8)
    h = hashlib.pbkdf2_hmac('sha256', pw.encode(), salt.encode(), 100000).hex()
    return f"pbkdf2${salt}${h}"

def check_pw(pw, stored):
    stored = stored or ""
    if stored.startswith("pbkdf2$"):
        try: _, salt, _h = stored.split("$", 2)
        except ValueError: return False
        return hmac.compare_digest(hash_pw(pw, salt), stored)
    return hmac.compare_digest(pw, stored)

def open_file(path):
    try:
        if sys.platform.startswith('win'): os.startfile(path)
        elif sys.platform == 'darwin': subprocess.Popen(['open', path])
        elif os.environ.get("ANDROID_ROOT") or os.environ.get("ANDROID_DATA"): return False
        else: subprocess.Popen(['xdg-open', path])
        return True
    except Exception: return False

# ═══════════════════════ دیتابیس ═══════════════════════
SCHEMA = """
CREATE TABLE IF NOT EXISTS companies (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL, reg_no TEXT, address TEXT, phone TEXT, email TEXT, website TEXT,
    economic_code TEXT, postal_code TEXT, sign_manager TEXT, sign_accountant TEXT,
    logo TEXT, insurance_rate REAL DEFAULT 7, employer_insurance_rate REAL DEFAULT 23,
    unemployment_rate REAL DEFAULT 3, admin_password TEXT DEFAULT 'pbkdf2$x$x',
    default_work_start TEXT DEFAULT '08:00', default_work_end TEXT DEFAULT '16:00',
    contract_template TEXT
);
CREATE TABLE IF NOT EXISTS departments (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, title TEXT, location TEXT, code TEXT,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS employees (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, personnel_code TEXT, national_code TEXT UNIQUE,
    first_name TEXT, last_name TEXT, father_name TEXT,
    id_number TEXT, id_issue_place TEXT, birth_date TEXT, birth_place TEXT,
    employment_date TEXT, contract_type TEXT DEFAULT 'رسمی', contract_end TEXT,
    dept_id INTEGER, job_title TEXT, education TEXT, insurance_number TEXT,
    daily_salary INTEGER, base_hours INTEGER DEFAULT NULL,
    marital INTEGER DEFAULT 0, child_count INTEGER DEFAULT 0,
    mobile TEXT, phone TEXT, address TEXT, postal_code TEXT,
    emergency_name TEXT, emergency_phone TEXT,
    card_number TEXT, account_number TEXT, iban TEXT, bank_name TEXT,
    tax_file_code TEXT, photo TEXT, notes TEXT,
    is_active INTEGER DEFAULT 1, created_at TEXT,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE,
    FOREIGN KEY(dept_id) REFERENCES departments(id) ON DELETE SET NULL
);
CREATE TABLE IF NOT EXISTS rate_years (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, year INTEGER,
    overtime_coeff REAL DEFAULT 1.4, night_coeff REAL DEFAULT 0.35,
    shift_percent REAL DEFAULT 15, friday_coeff REAL DEFAULT 0.4,
    holiday_coeff REAL DEFAULT 1.4, base_hours INTEGER DEFAULT 220,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS benefits (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, year INTEGER, title TEXT, amount INTEGER,
    taxable INTEGER DEFAULT 1, insurable INTEGER DEFAULT 1,
    monthly INTEGER DEFAULT 1, calc_type TEXT DEFAULT 'fixed',
    severance_basis INTEGER DEFAULT 0,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS benefit_exceptions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    benefit_id INTEGER, company_id INTEGER,
    emp_id INTEGER, dept_id INTEGER, reason TEXT,
    FOREIGN KEY(benefit_id) REFERENCES benefits(id) ON DELETE CASCADE,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS tax_brackets (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, year INTEGER,
    from_amount INTEGER, to_amount INTEGER, rate REAL,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS base_year_rules (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, year INTEGER,
    min_service INTEGER, max_service INTEGER, amount INTEGER,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS eid_rules (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, year INTEGER,
    min_days INTEGER, max_days INTEGER, daily_min_wage INTEGER,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS attendances (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, emp_id INTEGER, year INTEGER, month INTEGER,
    work_days REAL DEFAULT 0,
    overtime_hours REAL DEFAULT 0, night_hours REAL DEFAULT 0,
    absent_hours REAL DEFAULT 0, mission_days REAL DEFAULT 0,
    shift_percent REAL DEFAULT 0, friday_hours REAL DEFAULT 0,
    holiday_hours REAL DEFAULT 0,
    overtime_minutes INTEGER DEFAULT 0, night_minutes INTEGER DEFAULT 0,
    absent_minutes INTEGER DEFAULT 0, notes TEXT,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE,
    FOREIGN KEY(emp_id) REFERENCES employees(id) ON DELETE CASCADE,
    UNIQUE(company_id, emp_id, year, month)
);
CREATE TABLE IF NOT EXISTS loans (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, emp_id INTEGER,
    principal INTEGER, install_count INTEGER, each_amount REAL,
    start_year INTEGER, start_month INTEGER, remaining_balance INTEGER,
    purpose TEXT, status INTEGER DEFAULT 0,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE,
    FOREIGN KEY(emp_id) REFERENCES employees(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS loan_installments (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    loan_id INTEGER, installment_no INTEGER,
    due_year INTEGER, due_month INTEGER, amount REAL,
    is_paid INTEGER DEFAULT 0,
    status TEXT DEFAULT 'pending',
    original_due_year INTEGER,
    original_due_month INTEGER,
    defer_count INTEGER DEFAULT 0,
    calculated_payroll_id INTEGER,
    calculated_year INTEGER,
    calculated_month INTEGER,
    paid_payroll_id INTEGER,
    paid_year INTEGER,
    paid_month INTEGER,
    skip_reason TEXT,
    note TEXT,
    FOREIGN KEY(loan_id) REFERENCES loans(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS bonuses (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, emp_id INTEGER, year INTEGER, month INTEGER,
    amount INTEGER, reason TEXT, taxable INTEGER DEFAULT 1, insurable INTEGER DEFAULT 1,
    payment_status TEXT DEFAULT 'pending',
    paid_year INTEGER,
    paid_month INTEGER,
    paid_payroll_id INTEGER,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE,
    FOREIGN KEY(emp_id) REFERENCES employees(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS deductions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, emp_id INTEGER, year INTEGER, month INTEGER,
    amount INTEGER, reason TEXT,
    payment_status TEXT DEFAULT 'pending',
    applied_year INTEGER,
    applied_month INTEGER,
    applied_payroll_id INTEGER,
    note TEXT,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE,
    FOREIGN KEY(emp_id) REFERENCES employees(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS payrolls (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, year INTEGER, month INTEGER,
    emp_id INTEGER, dept_id INTEGER,
    daily_salary INTEGER, work_days REAL, base_salary_monthly INTEGER,
    overtime_amount INTEGER DEFAULT 0, night_amount INTEGER DEFAULT 0,
    shift_amount INTEGER DEFAULT 0, friday_amount INTEGER DEFAULT 0,
    holiday_amount INTEGER DEFAULT 0, mission_amount INTEGER DEFAULT 0,
    absent_ded INTEGER DEFAULT 0, benefits_sum INTEGER DEFAULT 0,
    base_year_amount INTEGER DEFAULT 0, bonus_amount INTEGER DEFAULT 0,
    deduction_amount INTEGER DEFAULT 0,
    gross_salary INTEGER, net_salary INTEGER,
    insurance_emp INTEGER, insurance_er INTEGER, tax INTEGER, loan_install INTEGER,
    overtime_hours REAL DEFAULT 0, night_hours REAL DEFAULT 0,
    absent_hours REAL DEFAULT 0, mission_days REAL DEFAULT 0,
    friday_hours REAL DEFAULT 0, holiday_hours REAL DEFAULT 0,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE,
    FOREIGN KEY(emp_id) REFERENCES employees(id) ON DELETE CASCADE,
    FOREIGN KEY(dept_id) REFERENCES departments(id) ON DELETE SET NULL
);
CREATE TABLE IF NOT EXISTS payroll_details (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    payroll_id INTEGER, name TEXT, amount INTEGER, type INTEGER,
    FOREIGN KEY(payroll_id) REFERENCES payrolls(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS accounting_entries (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, payroll_id INTEGER,
    entry_date TEXT, account_code TEXT, account_name TEXT,
    debit INTEGER, credit INTEGER, description TEXT,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE,
    FOREIGN KEY(payroll_id) REFERENCES payrolls(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS eid_records (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, emp_id INTEGER, year INTEGER,
    amount INTEGER, severance INTEGER, work_days REAL,
    monthly_salary INTEGER, notes TEXT,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE,
    FOREIGN KEY(emp_id) REFERENCES employees(id) ON DELETE CASCADE,
    UNIQUE(company_id, emp_id, year)
);
CREATE TABLE IF NOT EXISTS contracts (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, emp_id INTEGER, title TEXT, template TEXT,
    start_date TEXT, end_date TEXT, created_at TEXT,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE,
    FOREIGN KEY(emp_id) REFERENCES employees(id) ON DELETE CASCADE
);
CREATE INDEX IF NOT EXISTS idx_att ON attendances(company_id, year, month);
CREATE INDEX IF NOT EXISTS idx_pay ON payrolls(company_id, year, month);
CREATE INDEX IF NOT EXISTS idx_inst ON loan_installments(loan_id, due_year, due_month);
CREATE INDEX IF NOT EXISTS idx_emp_dept ON employees(dept_id);
"""

DEFAULT_CONTRACT = """قرارداد کار

این قرارداد فی‌مابین شرکت «{{company_name}}» به نشانی {{company_address}}، تلفن {{company_phone}}، به نمایندگی {{company_manager}} (کارفرما) از یک طرف، و آقای/خانم «{{first_name}} {{last_name}}» فرزند {{father_name}} به کد ملی {{national_code}}، شماره شناسنامه {{id_number}}، صادره از {{id_issue_place}}، متولد {{birth_date}}، محل تولد {{birth_place}}، ساکن {{address}}، تلفن همراه {{mobile}} (کارگر) از طرف دیگر، با رعایت ماده ۷ قانون کار جمهوری اسلامی ایران منعقد می‌گردد.

ماده ۱ — موضوع قرارداد:
انجام کار در سمت «{{job_title}}» در واحد «{{dept_title}}» طبق ضوابط کارفرما.

ماده ۲ — مدت قرارداد:
از تاریخ {{employment_date}} لغایت {{contract_end}}.

ماده ۳ — محل انجام کار:
{{company_address}} یا هر محلی که کارفرما تعیین نماید.

ماده ۴ — ساعات کار:
طبق ماده ۵۱ قانون کار، ۴۴ ساعت در هفته. از {{work_start}} تا {{work_end}}.

ماده ۵ — حقوق و مزایا:
حقوق روزانه {{daily_salary}} ریال معادل ماهانه {{monthly_salary}} ریال، به‌علاوه مزایای قانونی.

ماده ۶ — بیمه:
کارگر از بدو اشتغال تحت پوشش تأمین اجتماعی قرار می‌گیرد. شماره بیمه: {{insurance_number}}.

ماده ۷ — تعطیلات و مرخصی:
طبق مواد ۶۴ تا ۷۳ قانون کار.

ماده ۸ — فسخ قرارداد:
طبق مواد ۲۴ تا ۲۷ و ۴۱ قانون کار.

ماده ۹ — این قرارداد در ۹ ماده و دو نسخه تنظیم شد.

تاریخ انعقاد: {{today}}

کارفرما:                                     کارگر:
{{company_manager}}                          {{first_name}} {{last_name}}
"""

YEAR_TABLES = ('rate_years','benefits','tax_brackets','base_year_rules','eid_rules')

# نگاشت کامل مهاجرت‌ها برای دیتابیس‌های قدیمی
MIGRATIONS = {
    'companies': [('email','TEXT'),('website','TEXT'),('economic_code','TEXT'),
                  ('postal_code','TEXT'),('unemployment_rate','REAL DEFAULT 3'),
                  ('default_work_start',"TEXT DEFAULT '08:00'"),
                  ('default_work_end',"TEXT DEFAULT '16:00'"),
                  ('contract_template','TEXT')],
    'employees': [('personnel_code','TEXT'),('id_number','TEXT'),
                  ('id_issue_place','TEXT'),('birth_place','TEXT'),
                  ('contract_type',"TEXT DEFAULT 'رسمی'"),('contract_end','TEXT'),
                  ('education','TEXT'),('mobile','TEXT'),('phone','TEXT'),
                  ('address','TEXT'),('postal_code','TEXT'),
                  ('emergency_name','TEXT'),('emergency_phone','TEXT'),
                  ('bank_name','TEXT'),('tax_file_code','TEXT'),
                  ('photo','TEXT'),('notes','TEXT'),('created_at','TEXT'),
                  ('insurance_exempt','INTEGER DEFAULT 0'),
                  ('tax_exempt','INTEGER DEFAULT 0'),
                  ('shift_pattern',"TEXT DEFAULT 'none'")],
    'rate_years': [('holiday_coeff','REAL DEFAULT 1.4'),
                   ('min_daily_wage', 'INTEGER'),
                   ('housing_allowance', 'INTEGER'),
                   ('food_allowance', 'INTEGER'),
                   ('marriage_allowance', 'INTEGER'),
                   ('child_allowance', 'INTEGER'),
                   ('base_year_daily', 'INTEGER'),
                   ('hours_per_day', 'REAL'),
                   ('weekly_hours', 'REAL'),
                   ('insurance_cap_multiplier', 'REAL'),
                   ('insurance_employee_rate', 'REAL'),
                   ('insurance_employer_rate', 'REAL'),
                   ('insurance_unemployment_rate', 'REAL'),
                   ('shift_morning_evening', 'REAL'),
                   ('shift_three_turn', 'REAL'),
                   ('shift_morning_night', 'REAL'),
                   ('eid_min_days', 'INTEGER'),
                   ('eid_max_days', 'INTEGER'),
                   ('mission_daily_rate', 'INTEGER')],
    'benefits': [('monthly','INTEGER DEFAULT 1'),
                 ('calc_type',"TEXT DEFAULT 'fixed'"),
                 ('severance_basis','INTEGER DEFAULT 0')],
    'benefit_exceptions': [('emp_id','INTEGER'),('dept_id','INTEGER'),
                           ('reason','TEXT'),('benefit_id','INTEGER'),
                           ('company_id','INTEGER')],
    'attendances': [('work_days','REAL DEFAULT 0'),
                    ('overtime_hours','REAL DEFAULT 0'),
                    ('night_hours','REAL DEFAULT 0'),
                    ('absent_hours','REAL DEFAULT 0'),
                    ('mission_days','REAL DEFAULT 0'),
                    ('shift_percent','REAL DEFAULT 0'),
                    ('friday_hours','REAL DEFAULT 0'),
                    ('holiday_hours','REAL DEFAULT 0'),
                    ('overtime_minutes','INTEGER DEFAULT 0'),
                    ('night_minutes','INTEGER DEFAULT 0'),
                    ('absent_minutes','INTEGER DEFAULT 0'),
                    ('notes','TEXT'),
                    ('friday_rest_replaced','INTEGER DEFAULT 0'),
                    ('holiday_rest_replaced','INTEGER DEFAULT 0')],
    'loans': [('purpose','TEXT')],
    'loan_installments': [
        ('status', "TEXT DEFAULT 'pending'"),
        ('original_due_year', 'INTEGER'),
        ('original_due_month', 'INTEGER'),
        ('defer_count', 'INTEGER DEFAULT 0'),
        ('calculated_payroll_id', 'INTEGER'),
        ('calculated_year', 'INTEGER'),
        ('calculated_month', 'INTEGER'),
        ('paid_payroll_id', 'INTEGER'),
        ('paid_year', 'INTEGER'),
        ('paid_month', 'INTEGER'),
        ('skip_reason', 'TEXT'),
        ('note', 'TEXT'),
    ],
    'bonuses': [('reason','TEXT'),('taxable','INTEGER DEFAULT 1'),
                ('insurable','INTEGER DEFAULT 1'),
                ('payment_status', "TEXT DEFAULT 'pending'"),
                ('paid_year', 'INTEGER'),
                ('paid_month', 'INTEGER'),
                ('paid_payroll_id', 'INTEGER')],
    'deductions': [
        ('payment_status', "TEXT DEFAULT 'pending'"),
        ('applied_year', 'INTEGER'),
        ('applied_month', 'INTEGER'),
        ('applied_payroll_id', 'INTEGER'),
        ('note', 'TEXT'),
    ],
    'payrolls': [('holiday_amount','INTEGER DEFAULT 0'),
                 ('holiday_hours','REAL DEFAULT 0'),
                 ('bonus_amount','INTEGER DEFAULT 0'),
                 ('deduction_amount','INTEGER DEFAULT 0'),
                 ('benefits_sum','INTEGER DEFAULT 0'),
                 ('base_year_amount','INTEGER DEFAULT 0'),
                 ('payment_status', "TEXT DEFAULT 'unpaid'"),
                 ('payment_date', 'TEXT'),
                 ('payment_ref', 'TEXT'),
                 ('payment_note', 'TEXT'),
                 ('friday_rest_replaced', 'INTEGER DEFAULT 0'),
                 ('holiday_rest_replaced', 'INTEGER DEFAULT 0')],
    'eid_records': [('monthly_salary','INTEGER'),('notes','TEXT')],
}


class Database:
    def __init__(self, path=None):
        self.path = path or os.path.join(get_data_dir(), "payroll.db")
        self.init_db()

    def conn(self):
        c = sqlite3.connect(self.path, timeout=15)
        c.row_factory = sqlite3.Row
        c.execute("PRAGMA foreign_keys = ON")
        c.execute("PRAGMA synchronous = NORMAL")
        c.execute("PRAGMA temp_store = MEMORY")
        c.execute("PRAGMA busy_timeout = 15000")
        c.execute("PRAGMA cache_size = -12000")
        return c

    @contextmanager
    def tx(self):
        c = self.conn()
        try:
            yield c; c.commit()
        except Exception:
            c.rollback(); raise
        finally: c.close()

    def q(self, sql, p=()):
        c = self.conn()
        try: return [dict(r) for r in c.execute(sql, p).fetchall()]
        finally: c.close()

    def q1(self, sql, p=()):
        r = self.q(sql, p)
        return r[0] if r else None

    def x(self, sql, p=()):
        with self.tx() as c:
            return c.execute(sql, p).lastrowid

    def insert(self, table, data):
        cols = ",".join(data); ph = ",".join("?"*len(data))
        return self.x(f"INSERT INTO {table} ({cols}) VALUES ({ph})", tuple(data.values()))

    def update(self, table, rid, data):
        sets = ",".join(f"{k}=?" for k in data)
        self.x(f"UPDATE {table} SET {sets} WHERE id=?", (*data.values(), rid))

    def delete(self, table, rid):
        self.x(f"DELETE FROM {table} WHERE id=?", (rid,))

    def init_db(self):
        """ایجاد جداول جدید و مهاجرت امن جداول قدیمی."""
        c = self.conn()
        try:
            # گام ۱: ساخت همه جداول با schema جدید
            # (برای جداول موجود، CREATE TABLE IF NOT EXISTS کاری نمی‌کند)
            c.executescript(SCHEMA)
            c.commit()

            # گام ۲: افزودن ستون‌های جدید به جداول موجود
            existing_tables = {r[0] for r in c.execute(
                "SELECT name FROM sqlite_master WHERE type='table'").fetchall()}

            for tbl, cols in MIGRATIONS.items():
                if tbl not in existing_tables:
                    continue
                try:
                    info = c.execute(f'PRAGMA table_info("{tbl}")').fetchall()
                    existing_cols = {r[1] for r in info}
                    for col, typ in cols:
                        if col in existing_cols:
                            continue
                        try:
                            c.execute(f'ALTER TABLE "{tbl}" ADD COLUMN "{col}" {typ}')
                            log_error(f"✅ Migration: {tbl}.{col} added")
                        except sqlite3.OperationalError as ex:
                            log_error(f"⚠️ Migration {tbl}.{col}: {ex}")
                    c.commit()
                except Exception as ex:
                    log_error(f"⚠️ Migration table {tbl}: {ex}")

            try:
                c.execute("PRAGMA journal_mode = WAL")
                for ddl in (
                    "CREATE INDEX IF NOT EXISTS idx_emp_company ON employees(company_id, is_active)",
                    "CREATE INDEX IF NOT EXISTS idx_loans_company ON loans(company_id, emp_id)",
                    "CREATE INDEX IF NOT EXISTS idx_bon ON bonuses(company_id, year, month)",
                    "CREATE INDEX IF NOT EXISTS idx_ded ON deductions(company_id, year, month)",
                    "CREATE INDEX IF NOT EXISTS idx_pay_emp ON payrolls(emp_id)",
                    "CREATE INDEX IF NOT EXISTS idx_pd ON payroll_details(payroll_id)",
                    "CREATE INDEX IF NOT EXISTS idx_acc ON accounting_entries(payroll_id)"):
                    try: c.execute(ddl)
                    except Exception: pass
                c.commit()
            except Exception:
                pass
            row = c.execute("SELECT id FROM companies LIMIT 1").fetchone()
        finally:
            c.close()
        if not row:
            self.seed_defaults()

    def seed_defaults(self):
        cid = self.insert('companies', dict(
            name='شرکت من', reg_no='', address='', phone='', email='', website='',
            economic_code='', postal_code='', sign_manager='', sign_accountant='',
            insurance_rate=7, employer_insurance_rate=23, unemployment_rate=3,
            admin_password=hash_pw('1421'),
            default_work_start='08:00', default_work_end='16:00',
            contract_template=DEFAULT_CONTRACT))
        self.insert('departments', dict(company_id=cid, title='عمومی', location='', code='GEN'))
        y = STD['year']
        self.insert('rate_years', dict(company_id=cid, year=y, overtime_coeff=1.4,
                                       night_coeff=0.35, shift_percent=15,
                                       friday_coeff=0.4, holiday_coeff=1.4, base_hours=220))
        for t, a, tx_, ins, ct in (
            ('حق مسکن', STD['housing'], 1, 1, 'fixed'),
            ('بن کارگری', STD['food'], 1, 1, 'fixed'),
            ('حق تاهل', STD['marriage'], 1, 1, 'marital'),
            ('حق اولاد', STD['child_allowance'], 1, 0, 'child')):
            self.insert('benefits', dict(company_id=cid, year=y, title=t, amount=a,
                                         taxable=tx_, insurable=ins, monthly=1, calc_type=ct))
        for fa, ta, r in STD['tax_brackets']:
            self.insert('tax_brackets', dict(company_id=cid, year=y,
                                             from_amount=fa, to_amount=ta, rate=r))
        self.insert('base_year_rules', dict(company_id=cid, year=y, min_service=1,
                                            max_service=20, amount=STD['base_year_daily']))
        self.insert('eid_rules', dict(company_id=cid, year=y, min_days=60,
                                      max_days=90, daily_min_wage=STD['min_daily_wage']))

    def seed_sample(self, cid):
        if self.q1("SELECT id FROM employees WHERE company_id=?", (cid,)): return False
        ids = [self.insert('departments', dict(company_id=cid, title=t, location='', code=t[:3]))
               for t in ('اداری', 'فروش', 'فنی')]
        samples = [
            ('0012345678', 'رضا', 'محمدی', 'علی', '1365/05/10', '1399/01/01', ids[0],
             'مدیر مالی', '12345678901', 6_000_000, 1, 2, '09121111111'),
            ('0098765432', 'سارا', 'احمدی', 'محمود', '1370/02/15', '1400/05/10', ids[1],
             'کارشناس فروش', '12345678902', 4_666_667, 0, 0, '09122222222'),
            ('0034567891', 'محمد', 'کریمی', 'حسین', '1360/08/20', '1395/03/15', ids[2],
             'تکنسین فنی', '12345678903', 7_333_333, 1, 3, '09123333333'),
        ]
        for s in samples:
            eid = self.insert('employees', dict(
                company_id=cid, national_code=s[0], first_name=s[1], last_name=s[2],
                father_name=s[3], birth_date=s[4], employment_date=s[5], dept_id=s[6],
                job_title=s[7], insurance_number=s[8], daily_salary=s[9], marital=s[10],
                child_count=s[11], mobile=s[12], is_active=1,
                created_at=datetime.now().strftime('%Y/%m/%d')))
            self.upsert_attendance(cid, dict(emp_id=eid, year=STD['year'], month=1,
                work_days=22, overtime_hours=12, night_hours=6, absent_hours=0,
                mission_days=2, shift_percent=15, friday_hours=2, holiday_hours=0))
        return True

    def active_company(self):
        r = self.q1("SELECT id FROM companies ORDER BY id LIMIT 1")
        return r['id'] if r else None

    def company_data(self, cid, conn=None):
        own = conn is None
        c = conn or self.conn()
        try:
            def rows(sql, p=()):
                return [dict(r) for r in c.execute(sql, p).fetchall()]
            row = c.execute("SELECT * FROM companies WHERE id=?", (cid,)).fetchone()
            data = dict(row) if row else {}
            data['departments'] = rows("SELECT * FROM departments WHERE company_id=?", (cid,))
            data['employees'] = rows("SELECT * FROM employees WHERE company_id=? ORDER BY id", (cid,))
            data['rate_years'] = rows("SELECT * FROM rate_years WHERE company_id=? ORDER BY year", (cid,))
            data['benefits'] = rows("SELECT * FROM benefits WHERE company_id=?", (cid,))
            data['benefit_exceptions'] = rows("SELECT * FROM benefit_exceptions WHERE company_id=?", (cid,))
            data['tax_brackets'] = rows("SELECT * FROM tax_brackets WHERE company_id=? ORDER BY year, from_amount", (cid,))
            data['base_year_rules'] = rows("SELECT * FROM base_year_rules WHERE company_id=? ORDER BY year", (cid,))
            data['eid_rules'] = rows("SELECT * FROM eid_rules WHERE company_id=? ORDER BY year", (cid,))
            data['attendances'] = rows("SELECT * FROM attendances WHERE company_id=?", (cid,))
            data['loans'] = rows("SELECT * FROM loans WHERE company_id=? ORDER BY id DESC", (cid,))
            data['loan_installments'] = rows(
                "SELECT li.*, l.emp_id FROM loan_installments li "
                "JOIN loans l ON li.loan_id=l.id WHERE l.company_id=?", (cid,))
            data['bonuses'] = rows("SELECT * FROM bonuses WHERE company_id=?", (cid,))
            data['deductions'] = rows("SELECT * FROM deductions WHERE company_id=?", (cid,))
            data['eid_records'] = rows("SELECT * FROM eid_records WHERE company_id=?", (cid,))
            data['contracts'] = rows("SELECT * FROM contracts WHERE company_id=?", (cid,))
            return data
        finally:
            if own: c.close()

    def upsert_attendance(self, cid, a):
        self.x("""INSERT INTO attendances (company_id, emp_id, year, month,
            work_days, overtime_hours, night_hours, absent_hours, mission_days,
            shift_percent, friday_hours, holiday_hours,
            overtime_minutes, night_minutes, absent_minutes, friday_rest_replaced, holiday_rest_replaced, notes)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
            ON CONFLICT(company_id, emp_id, year, month) DO UPDATE SET
            work_days=excluded.work_days, overtime_hours=excluded.overtime_hours,
            night_hours=excluded.night_hours, absent_hours=excluded.absent_hours,
            mission_days=excluded.mission_days, shift_percent=excluded.shift_percent,
            friday_hours=excluded.friday_hours, holiday_hours=excluded.holiday_hours,
            overtime_minutes=excluded.overtime_minutes, night_minutes=excluded.night_minutes,
            absent_minutes=excluded.absent_minutes, friday_rest_replaced=excluded.friday_rest_replaced,
            holiday_rest_replaced=excluded.holiday_rest_replaced, notes=excluded.notes""",
            (cid, a['emp_id'], a['year'], a['month'],
             a.get('work_days', 0), a.get('overtime_hours', 0), a.get('night_hours', 0),
             a.get('absent_hours', 0), a.get('mission_days', 0),
             a.get('shift_percent', 0), a.get('friday_hours', 0), a.get('holiday_hours', 0),
             a.get('overtime_minutes', 0), a.get('night_minutes', 0),
             a.get('absent_minutes', 0), a.get('friday_rest_replaced', 0), a.get('holiday_rest_replaced', 0), a.get('notes', '')))

    def save_loan(self, cid, emp_id, principal, count, sy, sm, purpose=''):
        each = principal // count
        with self.tx() as c:
            lid = c.execute("""INSERT INTO loans (company_id, emp_id, principal, install_count,
                each_amount, start_year, start_month, remaining_balance, purpose, status)
                VALUES (?,?,?,?,?,?,?,?,?,0)""",
                (cid, emp_id, principal, count, each, sy, sm, principal, purpose)).lastrowid
            for i in range(count):
                dy = sy + ((sm + i - 1) // 12)
                dm = ((sm + i - 1) % 12) + 1
                amt = each if i < count - 1 else principal - each * (count - 1)
                c.execute("""INSERT INTO loan_installments
                    (loan_id, installment_no, due_year, due_month, amount, is_paid,
                     status, original_due_year, original_due_month, defer_count)
                    VALUES (?,?,?,?,?,0,'pending',?,?,0)""",
                    (lid, i + 1, dy, dm, amt, dy, dm))
        return lid

    def copy_year(self, cid, src, dst):
        n = 0
        with self.tx() as c:
            for table in YEAR_TABLES:
                if c.execute(f"SELECT 1 FROM {table} WHERE company_id=? AND year=? LIMIT 1",
                             (cid, dst)).fetchone(): continue
                for r in c.execute(f"SELECT * FROM {table} WHERE company_id=? AND year=?", (cid, src)).fetchall():
                    d = dict(r); d.pop('id', None); d['year'] = dst
                    c.execute(f"INSERT INTO {table} ({','.join(d)}) VALUES ({','.join('?'*len(d))})",
                              tuple(d.values()))
                    n += 1
        return n

    def previous_settings_year(self, cid, year):
        r = self.q1("SELECT MAX(year) AS y FROM rate_years WHERE company_id=? AND year<?", (cid, year))
        return r['y'] if r and r['y'] else None

    def backup(self):
        dst = os.path.join(export_dir(), f"backup_{datetime.now():%Y%m%d_%H%M%S}.db")
        src = sqlite3.connect(self.path); out = sqlite3.connect(dst)
        try: src.backup(out)
        finally: out.close(); src.close()
        return dst

    def restore(self, src_path):
        t = sqlite3.connect(src_path)
        try: t.execute("SELECT 1 FROM companies LIMIT 1")
        finally: t.close()
        keep = sqlite3.connect(self.path); out = sqlite3.connect(self.path + ".before_restore")
        try: keep.backup(out)
        finally: out.close(); keep.close()
        for ext in ("-wal", "-shm"):
            try: os.remove(self.path + ext)
            except OSError: pass
        shutil.copy2(src_path, self.path)
        self.init_db()

# ═══════════════════════ موتور محاسبات ═══════════════════════
class PayrollCalculator:
    def __init__(self, company, year, month):
        self.company = company; self.year = year; self.month = month
        self.dim = days_in_month(year, month)
        rates = self._nearest(company.get('rate_years', []), year)
        self.rate = rates[0] if rates else {}
        self.overtime_coeff = self._p(self.rate.get('overtime_coeff'), 1.4)
        self.night_coeff = self._prem(self.rate.get('night_coeff'), 0.35)
        self.friday_coeff = self._prem(self.rate.get('friday_coeff'), 0.40)
        self.holiday_coeff = self._prem(self.rate.get('holiday_coeff'), 1.4)
        self.shift_percent_default = self.rate.get('shift_percent') or 15
        self.default_base_hours = self.rate.get('base_hours') or 220
        self.insurance_rate = company.get('insurance_rate', 7)
        self.employer_insurance_rate = company.get('employer_insurance_rate', 23)
        self.unemployment_rate = company.get('unemployment_rate', 3)
        self.tax_brackets = sorted(self._nearest(company.get('tax_brackets', []), year),
                                   key=lambda b: b['from_amount'])
        self.base_year_rules = self._nearest(company.get('base_year_rules', []), year)
        self.eid_rules = self._nearest(company.get('eid_rules', []), year)
        self.benefits = self._nearest(company.get('benefits', []), year)
        self.benefit_exceptions = company.get('benefit_exceptions', []) or []
        self.min_daily_wage = (self.eid_rules[0].get('daily_min_wage')
                               if self.eid_rules else STD['min_daily_wage'])
        self.insurance_cap = 7 * self.min_daily_wage * self.dim

    @staticmethod
    def _p(v, d):
        if v in (None, 0): return d
        return v if v > 1 else v + 1

    @staticmethod
    def _prem(v, d):
        if v in (None, 0): return d
        if v >= 2: return v / 100
        if v > 1: return v - 1
        return v

    def _nearest(self, rows, year):
        exact = [r for r in rows if r.get('year') == year]
        if exact: return exact
        ys = [r['year'] for r in rows if r.get('year') and r['year'] <= year]
        if not ys: return []
        mx = max(ys)
        return [r for r in rows if r.get('year') == mx]

    def _benefit(self, title):
        for b in self.benefits:
            if b.get('title') == title:
                return b.get('amount', 0), bool(b.get('taxable')), bool(b.get('insurable', True))
        return 0, False, True

    def _is_excepted(self, benefit_id, emp, dept_id):
        """آیا این مزایا برای این پرسنل/دپارتمان استثنا شده؟"""
        for ex in self.benefit_exceptions:
            if ex.get('benefit_id') != benefit_id: continue
            ex_emp = ex.get('emp_id'); ex_dept = ex.get('dept_id')
            if ex_emp and int(ex_emp) == int(emp.get('id') or 0): return True
            if ex_dept and dept_id and int(ex_dept) == int(dept_id): return True
        return False

    def service_years(self, emp, month=None):
        d = emp.get('employment_date') or ''
        try:
            parts = d.split('/'); ey = int(parts[0]); em = int(parts[1]) if len(parts) >= 2 else 1
        except (ValueError, IndexError): return 0
        y = self.year - ey
        if em > (month or self.month): y -= 1
        return max(0, y)

    def base_year_bonus(self, emp, work_days):
        sy = self.service_years(emp)
        if sy < 1: return 0
        match = [r for r in self.base_year_rules
                 if (r.get('min_service') or 1) <= sy <= (r.get('max_service') or 99)]
        daily = (match[-1].get('amount') if match else None) or STD['base_year_daily']
        return rnd(daily * max(work_days or 0, 0))

    def daily_fixed(self, emp):
        by = self.base_year_bonus(emp, 30)
        return (emp.get('daily_salary') or 0) + (by / 30 if by > 0 else 0)

    def base_hours(self, emp):
        h = emp.get('base_hours')
        return int(h) if h and h > 0 else self.default_base_hours

    def hourly_rate(self, emp):
        return self.daily_fixed(emp) / getattr(self, 'hours_per_day', STD['hours_per_day'])

    def child_allowance(self, emp, work_days, dim=None):
        n = emp.get('child_count') or 0
        if n == 0: return 0
        per, _, _ = self._benefit('حق اولاد')
        if per <= 0: per = STD['child_allowance']
        return rnd(per * n * (work_days / (dim or self.dim)))

    def other_benefits_monthly(self, emp, days=30, dept_id=None):
        total = 0
        for b in self.benefits:
            t = b.get('title'); amt = b.get('amount') or 0
            if t == 'حق اولاد' or amt <= 0: continue
            if self._is_excepted(b['id'], emp, dept_id): continue
            if t == 'حق تاهل' and not emp.get('marital'): continue
            total += amt * days / 30
        return total

    def insurance(self, gross, rate):
        if gross <= 0: return 0
        return rnd(min(gross, self.insurance_cap) * rate / 100)

    def monthly_tax(self, taxable):
        if taxable <= 0 or not self.tax_brackets: return 0
        tax = 0
        for b in self.tax_brackets:
            frm = b['from_amount'] or 0
            to = b['to_amount'] if b['to_amount'] is not None else float('inf')
            if taxable <= frm: continue
            part = min(taxable, to) - frm
            if part > 0: tax += part * (b['rate'] or 0) / 100
        return rnd(tax)

    def compute_salary(self, emp, att, installments=None, bonuses=None, deductions=None):
        dept_id = emp.get('dept_id')
        wd = max(att.get('work_days', 0) or 0, 0)
        daily = emp.get('daily_salary') or 0
        base = rnd(daily * wd)

        def th(h_key, m_key):
            return (att.get(h_key, 0) or 0) + (att.get(m_key, 0) or 0) / 60.0

        ot_h = th('overtime_hours', 'overtime_minutes')
        ng_h = th('night_hours', 'night_minutes')
        ab_h = th('absent_hours', 'absent_minutes')
        fd_h = att.get('friday_hours', 0) or 0
        hl_h = att.get('holiday_hours', 0) or 0
        md_d = att.get('mission_days', 0) or 0
        sp = att.get('shift_percent', 0) or 0

        hourly = self.hourly_rate(emp)
        overtime = rnd(hourly * self.overtime_coeff * ot_h) if ot_h > 0 else 0
        night = rnd(hourly * self.night_coeff * ng_h) if ng_h > 0 else 0
        absent = rnd(hourly * ab_h) if ab_h > 0 else 0
        shift = rnd(self.daily_fixed(emp) * wd * sp / 100) if sp > 0 else 0
        friday = rnd(hourly * (1 + self.friday_coeff) * fd_h) if fd_h > 0 else 0
        holiday = rnd(hourly * (1 + self.holiday_coeff) * hl_h) if hl_h > 0 else 0
        mission = rnd(self.daily_fixed(emp) * md_d) if md_d > 0 else 0

        items = []; tot_all = tot_ins = tot_nontax = 0

        def add(name, amt, taxable, insurable):
            nonlocal tot_all, tot_ins, tot_nontax
            items.append({'name': name, 'amount': amt, 'taxable': taxable, 'insurable': insurable})
            tot_all += amt
            if insurable: tot_ins += amt
            if not taxable: tot_nontax += amt

        for b in self.benefits:
            if b['title'] == 'حق اولاد': continue
            if self._is_excepted(b['id'], emp, dept_id): continue
            if b['title'] == 'حق تاهل' and not emp.get('marital'): continue
            if (b.get('amount') or 0) <= 0: continue
            pr = rnd(b['amount'] * (wd / self.dim))
            if pr > 0:
                add(b['title'], pr, bool(b.get('taxable')), bool(b.get('insurable', True)))

        bonus = sum(x['amount'] for x in (bonuses or [])
                    if x.get('year') == self.year and x.get('month') == self.month
                    and x.get('emp_id') == emp['id'])
        if bonus > 0: add('پاداش', bonus, True, True)

        deduct = sum(x['amount'] for x in (deductions or [])
                     if x.get('year') == self.year and x.get('month') == self.month
                     and x.get('emp_id') == emp['id'])

        by = self.base_year_bonus(emp, wd)
        if by > 0: add('پایه سنوات', by, True, True)

        ch = self.child_allowance(emp, wd)
        if ch > 0:
            # خواندن وضعیت بیمه‌ای حق اولاد از تنظیمات مزایا
            child_insurable = False
            child_taxable = True
            for b in self.benefits:
                if b.get('title') == 'حق اولاد' or b.get('calc_type') == 'child':
                    child_insurable = bool(b.get('insurable', 0))
                    child_taxable = bool(b.get('taxable', 1))
                    break
            add('حق اولاد', ch, child_taxable, child_insurable)

        gross = base + overtime + night + shift + friday + holiday + mission + tot_all
        taxable = max(gross - mission - tot_nontax - deduct, 0)
        insurable = base + overtime + night + shift + friday + holiday + tot_ins
        ins_emp = self.insurance(insurable, self.insurance_rate)
        ins_er = self.insurance(insurable, self.employer_insurance_rate)
        tax = self.monthly_tax(taxable)

        loan, loan_ids = 0, []
        for i in (installments or []):
            if (i.get('due_year') == self.year and i.get('due_month') == self.month
                    and not i.get('is_paid') and i.get('emp_id') == emp['id']):
                loan += i.get('amount', 0); loan_ids.append(i['id'])
        loan = rnd(loan)

        net = gross - (ins_emp + tax + absent + loan + deduct)
        return {
            'gross': rnd(gross), 'net': rnd(net),
            'insurance_emp': ins_emp, 'insurance_er': ins_er, 'tax': tax,
            'overtime': overtime, 'shift': shift, 'night': night,
            'mission': mission, 'friday_work': friday, 'holiday_work': holiday,
            'absent_ded': absent, 'loan_install': loan, 'loan_inst_ids': loan_ids,
            'benefits_list': items,
            'base_salary_monthly': base, 'work_days': wd,
            'overtime_hours': ot_h, 'night_hours': ng_h, 'absent_hours': ab_h,
            'mission_days': md_d, 'friday_hours': fd_h, 'holiday_hours': hl_h,
            'bonus_amount': bonus, 'deduction_amount': deduct,
            'base_year_amount': by, 'taxable_gross': rnd(taxable)}


def _year_work_days(emp, year, company):
    # Wage-eligible days accumulated from the monthly timesheet, capped at the Jalali year length.
    total = sum(max(0.0, _as_float(a.get('work_days', 0)))
                for a in company.get('attendances', [])
                if a['emp_id'] == emp['id'] and a['year'] == year)
    return min(total, days_in_year(year))

def calc_eid(emp, year, company):
    c = PayrollCalculator(company, year, 1)
    wd = _year_work_days(emp, year, company)
    if wd <= 0: return 0
    rule = c.eid_rules[0] if c.eid_rules else {}
    ent = rule.get('min_days') or 60
    cap = rule.get('max_days') or 90
    dw = max(emp.get('daily_salary') or 0, 0)
    return rnd(min(dw * ent, c.min_daily_wage * cap) * min(wd / 365, 1))

def calc_severance(emp, year, company):
    c = PayrollCalculator(company, year, 1)
    monthly = ((emp.get('daily_salary') or 0) * 30 + c.base_year_bonus(emp, 30)
               + c.other_benefits_monthly(emp, 30)
               + c.child_allowance(emp, 30, dim=30))
    wd = _year_work_days(emp, year, company)
    return rnd(monthly * wd / 365)

def accounting_entries(pid, year, month, emp, r):
    d = f"{year}-{month:02d}-01"
    nm = f"{emp['first_name']} {emp['last_name']}"
    rows = [('800101', 'هزینه حقوق', r['gross'], 0, f'حقوق {nm}'),
            ('210101', 'حقوق پرداختنی', 0, r['net'], f'خالص حقوق {nm}')]
    if r['tax'] > 0: rows.append(('210102', 'مالیات پرداختنی', 0, r['tax'], 'مالیات'))
    if r['insurance_emp'] > 0:
        rows.append(('210103', 'بیمه سهم کارگر', 0, r['insurance_emp'], 'بیمه کارگر'))
    if r['loan_install'] > 0:
        rows.append(('210104', 'اقساط وام', 0, r['loan_install'], 'قسط'))
    if r['absent_ded'] > 0:
        rows.append(('210105', 'کسر کار', 0, r['absent_ded'], 'کسر'))
    if r['insurance_er'] > 0:
        rows.append(('800102', 'هزینه بیمه کارفرما', r['insurance_er'], 0, f'بیمه کارفرما {nm}'))
        rows.append(('210106', 'بیمه کارفرما پرداختنی', 0, r['insurance_er'], 'بیمه کارفرما'))
    return [dict(payroll_id=pid, entry_date=d, account_code=a, account_name=b,
                 debit=c_, credit=e, description=f) for a, b, c_, e, f in rows]


class PayrollService:
    def __init__(self, db): self.db = db

    def _reverse_and_delete(self, c, cid, year, month, only_unpaid=False):
        if only_unpaid:
            old = c.execute(
                "SELECT id, emp_id, loan_install FROM payrolls "
                "WHERE company_id=? AND year=? AND month=? "
                "AND (payment_status IS NULL OR payment_status<>'paid')",
                (cid, year, month)).fetchall()
        else:
            old = c.execute(
                "SELECT id, emp_id, loan_install FROM payrolls "
                "WHERE company_id=? AND year=? AND month=?",
                (cid, year, month)).fetchall()

        # 🆕 برگرداندن اقساط از حالت calculated → pending
        for p in old:
            c.execute("""UPDATE loan_installments
                SET status='pending',
                    calculated_payroll_id=NULL,
                    calculated_year=NULL,
                    calculated_month=NULL
                WHERE calculated_payroll_id=? AND status='calculated'""",
                (p['id'],))

        # برگرداندن اقساط پرداخت‌شده قدیمی (سازگاری با داده‌های قبل)
        for p in old:
            if (p['loan_install'] or 0) > 0:
                rows = c.execute("""SELECT li.id, li.amount, li.loan_id
                    FROM loan_installments li
                    JOIN loans l ON l.id=li.loan_id
                    WHERE l.company_id=? AND l.emp_id=? AND li.due_year=?
                      AND li.due_month=? AND li.is_paid=1
                      AND li.paid_payroll_id IS NULL""",
                    (cid, p['emp_id'], year, month)).fetchall()
                for r in rows:
                    c.execute("UPDATE loan_installments SET is_paid=0, status='pending' WHERE id=?",
                              (r['id'],))
                    c.execute("UPDATE loans SET remaining_balance=remaining_balance+?, status=0 WHERE id=?",
                              (rnd(r['amount']), r['loan_id']))

        for p in old:
            c.execute("DELETE FROM accounting_entries WHERE payroll_id=?", (p['id'],))
            c.execute("DELETE FROM payroll_details WHERE payroll_id=?", (p['id'],))
            c.execute("DELETE FROM payrolls WHERE id=?", (p['id'],))
        return len(old)

    def delete_month(self, cid, year, month):
        with self.db.tx() as c:
            return self._reverse_and_delete(c, cid, year, month)

    def calculate(self, cid, year, month, only_unpaid=False):
        with self.db.tx() as c:
            # برگشت فیش‌های قبلی (پرداخت‌نشده‌ها اگر only_unpaid=True)
            self._reverse_and_delete(c, cid, year, month, only_unpaid=only_unpaid)

            paid_emp_ids = set()
            if only_unpaid:
                paid_rows = c.execute(
                    "SELECT emp_id FROM payrolls "
                    "WHERE company_id=? AND year=? AND month=? AND payment_status='paid'",
                    (cid, year, month)).fetchall()
                paid_emp_ids = {r[0] for r in paid_rows}

            company = self.db.company_data(cid, conn=c)
            calc = PayrollCalculator(company, year, month)
            atts = {a['emp_id']: a for a in company['attendances']
                    if a['year'] == year and a['month'] == month}
            count = 0
            for emp in company['employees']:
                if not emp['is_active'] or emp['id'] not in atts: continue
                if emp['id'] in paid_emp_ids: continue

                r = calc.compute_salary(
                    emp, atts[emp['id']],
                    company['loan_installments'],
                    company['bonuses'],
                    company.get('deductions', []))

                pid = c.execute("""INSERT INTO payrolls (
                    company_id, year, month, emp_id, dept_id, daily_salary, work_days,
                    base_salary_monthly, overtime_amount, night_amount, shift_amount,
                    friday_amount, holiday_amount, mission_amount, absent_ded,
                    benefits_sum, base_year_amount, bonus_amount, deduction_amount,
                    gross_salary, net_salary, insurance_emp, insurance_er, tax,
                    loan_install, overtime_hours, night_hours, absent_hours,
                    mission_days, friday_hours, holiday_hours,
                    friday_rest_replaced, holiday_rest_replaced)
                    VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                    (cid, year, month, emp['id'], emp.get('dept_id'), emp.get('daily_salary'),
                     r['work_days'], r['base_salary_monthly'], r['overtime'], r['night'],
                     r['shift'], r['friday_work'], r['holiday_work'], r['mission'],
                     r['absent_ded'],
                     sum(x['amount'] for x in r['benefits_list'] if x['amount'] > 0),
                     r['base_year_amount'], r['bonus_amount'], r['deduction_amount'],
                     r['gross'], r['net'], r['insurance_emp'], r['insurance_er'], r['tax'],
                     r['loan_install'], r['overtime_hours'], r['night_hours'], r['absent_hours'],
                     r['mission_days'], r['friday_hours'], r['holiday_hours'],
                     r['friday_rest_replaced'], r['holiday_rest_replaced'])).lastrowid

                # 🆕 علامت‌گذاری اقساط وام محاسبه‌شده در این فیش
                for lid in r.get('loan_inst_ids') or []:
                    c.execute("""UPDATE loan_installments
                        SET status='calculated',
                            calculated_payroll_id=?,
                            calculated_year=?,
                            calculated_month=?
                        WHERE id=?
                          AND (status IS NULL OR status NOT IN ('paid','skipped','waived'))""",
                        (pid, year, month, lid))

                # 🆕 علامت‌گذاری پاداش‌های اعمال‌شده
                for b in (company.get('bonuses') or []):
                    if (b.get('emp_id') == emp['id']
                            and b.get('year') == year
                            and b.get('month') == month):
                        c.execute("""UPDATE bonuses
                            SET payment_status='calculated',
                                paid_payroll_id=?
                            WHERE id=? AND (payment_status IS NULL OR payment_status='pending')""",
                            (pid, b['id']))

                # 🆕 علامت‌گذاری کسورات اعمال‌شده
                for d in (company.get('deductions') or []):
                    if (d.get('emp_id') == emp['id']
                            and d.get('year') == year
                            and d.get('month') == month):
                        c.execute("""UPDATE deductions
                            SET payment_status='applied',
                                applied_payroll_id=?,
                                applied_year=?,
                                applied_month=?
                            WHERE id=? AND (payment_status IS NULL OR payment_status='pending')""",
                            (pid, year, month, d['id']))

                # جزئیات
                det = [(b['name'], b['amount'], 1 if b['amount'] >= 0 else 2)
                       for b in r['benefits_list']]
                det += [('بیمه سهم کارگر', r['insurance_emp'], 2),
                        ('مالیات حقوق', r['tax'], 2),
                        ('کسر کار', r['absent_ded'], 2)]
                if r['loan_install']: det.append(('قسط وام', r['loan_install'], 2))
                if r.get('deduction_amount'): det.append(('سایر کسورات', r['deduction_amount'], 2))
                for n, a, t in det:
                    c.execute("""INSERT INTO payroll_details
                        (payroll_id, name, amount, type) VALUES (?,?,?,?)""",
                        (pid, n, a, t))
                for e in accounting_entries(pid, year, month, emp, r):
                    c.execute("""INSERT INTO accounting_entries
                        (company_id, payroll_id, entry_date, account_code, account_name,
                         debit, credit, description) VALUES (?,?,?,?,?,?,?,?)""",
                        (cid, pid, e['entry_date'], e['account_code'], e['account_name'],
                         e['debit'], e['credit'], e['description']))
                count += 1
            return count

    def calculate_eid(self, cid, year):
        company = self.db.company_data(cid)
        n = 0
        with self.db.tx() as c:
            for emp in company['employees']:
                if not emp['is_active']: continue
                wd = _year_work_days(emp, year, company)
                c.execute("DELETE FROM eid_records WHERE company_id=? AND emp_id=? AND year=?",
                          (cid, emp['id'], year))
                annual_calc = PayrollCalculator(company, year, 1)
                monthly = (_last_wage_basis_monthly(annual_calc, emp)
                           if '_last_wage_basis_monthly' in globals()
                           else rnd((emp.get('daily_salary') or 0) * 30 + annual_calc.base_year_bonus(emp, 30)))
                c.execute("""INSERT INTO eid_records
                    (company_id, emp_id, year, amount, severance, work_days, monthly_salary)
                    VALUES (?,?,?,?,?,?,?)""",
                    (cid, emp['id'], year, calc_eid(emp, year, company),
                     calc_severance(emp, year, company), wd, monthly))
                n += 1
        return n

    def payrolls(self, cid, year, month):
        return self.db.q("SELECT * FROM payrolls WHERE company_id=? AND year=? AND month=? ORDER BY emp_id",
                         (cid, year, month))

    def details(self, pid):
        return self.db.q("SELECT * FROM payroll_details WHERE payroll_id=? ORDER BY id", (pid,))

# ═══════════════════════ CSV ═══════════════════════
def write_csv(path, header, rows):
    with open(path, 'w', newline='', encoding='utf-8-sig') as f:
        w = csv.writer(f); w.writerow(header); w.writerows(rows)

def export_full_csv(db, svc, cid, year, month):
    c = db.company_data(cid)
    emps = {e['id']: e for e in c['employees']}
    depts = {d['id']: d for d in c['departments']}
    pays = svc.payrolls(cid, year, month)
    header = ['ردیف','کد','نام','فامیل','کد ملی','دپارتمان','شغل','تاریخ استخدام',
              'روز کارکرد','حقوق روزانه','پایه ماهانه','ساعت اضافه','مبلغ اضافه',
              'ساعت شب','مبلغ شب','مبلغ نوبت','جمعه‌کاری','تعطیل‌کاری','مأموریت',
              'مزایا','سنوات','پاداش','ناخالص','بیمه کارگر','بیمه کارفرما',
              'مالیات','وام','کسرات','خالص']
    rows = []
    for i, p in enumerate(pays, 1):
        e = emps.get(p['emp_id']) or {}
        rows.append([i, p['emp_id'], e.get('first_name',''), e.get('last_name',''),
                     e.get('national_code',''),
                     (depts.get(p.get('dept_id')) or {}).get('title',''),
                     e.get('job_title',''), e.get('employment_date',''), p['work_days'],
                     e.get('daily_salary',0), p['base_salary_monthly'],
                     hours_to_hm(p.get('overtime_hours',0)), p.get('overtime_amount',0),
                     hours_to_hm(p.get('night_hours',0)), p.get('night_amount',0),
                     p.get('shift_amount',0), p.get('friday_amount',0),
                     p.get('holiday_amount',0), p.get('mission_amount',0),
                     p.get('benefits_sum',0), p.get('base_year_amount',0),
                     p.get('bonus_amount',0), p['gross_salary'], p['insurance_emp'],
                     p['insurance_er'], p['tax'], p['loan_install'], p['absent_ded'],
                     p['net_salary']])
    path = os.path.join(export_dir(), f"payroll_full_{year}_{month:02d}_{datetime.now():%Y%m%d_%H%M%S}.csv")
    write_csv(path, header, rows)
    return path

def export_attendance_csv(db, cid, year, month, employees, att_map):
    """خروجی کارکرد؛ ستون‌های ساعت/دقیقه را مطابق ورودی جدول به هم تبدیل می‌کند."""
    rows = []
    def combined_hours(a, hour_key, minute_key):
        total = max(0.0, _as_float(a.get(hour_key)) + _as_float(a.get(minute_key)) / 60.0)
        return hours_to_hm(total)
    for i, e in enumerate(employees, 1):
        a = att_map.get(e['id'], {})
        rows.append([i, e['id'], e.get('personnel_code') or '', e.get('first_name',''),
                     e.get('last_name',''), e.get('national_code',''), a.get('work_days',0),
                     combined_hours(a, 'overtime_hours', 'overtime_minutes'),
                     combined_hours(a, 'night_hours', 'night_minutes'),
                     combined_hours(a, 'absent_hours', 'absent_minutes'),
                     a.get('mission_days',0), a.get('shift_percent',0),
                     a.get('friday_hours',0), a.get('holiday_hours',0),
                     a.get('friday_rest_replaced', 0),
                     a.get('holiday_rest_replaced', 0), a.get('notes', '')])
    path = os.path.join(export_dir(), f"timesheet_{year}_{month:02d}_{datetime.now():%Y%m%d_%H%M%S}.csv")
    write_csv(path, ['ردیف','کد پرسنلی','نام','نام خانوادگی','کد ملی','روز کارکرد',
                     'اضافه‌کاری (ساعت:دقیقه)','شب‌کاری (ساعت:دقیقه)','کسرکار (ساعت:دقیقه)',
                     'مأموریت (روز)','نوبت‌کاری (%)','جمعه‌کاری (ساعت)','تعطیل‌کاری (ساعت)',
                     'استراحت جایگزین جمعه','استراحت جایگزین تعطیل','توضیحات'], rows)
    return path

# ═══════════════════════ PDF ═══════════════════════
_MIRROR = str.maketrans("()[]{}<>", ")(][}{><")
_LTR_RUN = re.compile(r'[0-9A-Za-z][0-9A-Za-z.,:/%\-_]*')

def _simple_bidi(s):
    """پردازش هر خط جداگانه تا ترتیب خطوط حفظ شود."""
    out = []
    for line in str(s).split('\n'):
        out.append(_LTR_RUN.sub(lambda m: m.group(0)[::-1],
                                line[::-1]).translate(_MIRROR))
    return '\n'.join(out)
def rtl(s):
    s = str(s)
    if _reshaper is None: return s
    try:
        shaped = _reshaper.reshape(s)
        if _get_display is not None: return _get_display(shaped)
        return _simple_bidi(shaped)
    except Exception: return s

def find_font():
    cands = []
    for base in (HERE, os.path.dirname(HERE)):
        for sub in (("fonts",), ("assets", "fonts")):
            cands.append(os.path.join(base, *sub, "Vazirmatn-Regular.ttf"))
    cands += glob.glob("/system/fonts/*Naskh*Arabic*Regular*.ttf")
    cands += glob.glob("/system/fonts/*Sans*Arabic*Regular*.ttf")
    cands += glob.glob("/system/fonts/*Arabic*.ttf")
    cands += ["/system/fonts/DroidSansArabic.ttf",
              "C:/Windows/Fonts/tahoma.ttf", "C:/Windows/Fonts/arial.ttf",
              "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"]
    for p in cands:
        if os.path.isfile(p) and p.lower().endswith(".ttf"): return p
    return None

def _pdf_init(size=(148, 210)):
    from fpdf import FPDF
    if _reshaper is None: raise RuntimeError("arabic-reshaper نصب نیست")
    font = find_font()
    if not font: raise RuntimeError("فونت فارسی پیدا نشد. Vazirmatn-Regular.ttf را در assets/fonts بگذارید.")
    pdf = FPDF(orientation="P", unit="mm", format=size)
    pdf.set_auto_page_break(False)
    pdf.add_font("F", "", font)
    return pdf, font

def _draw_logo(pdf, logo_b64, x, y, w=18, h=18):
    if not logo_b64 or Image is None: return False
    try:
        if logo_b64.startswith('data:'): logo_b64 = logo_b64.split(',', 1)[1]
        data = base64.b64decode(logo_b64)
        img = Image.open(io.BytesIO(data)).convert('RGB')
        tmp = os.path.join(tempfile.gettempdir(), 'logo_tmp.png')
        img.save(tmp)
        pdf.image(tmp, x=x, y=y, w=w, h=h)
        return True
    except Exception: return False

def build_pdf(path, company, slips):
    pdf, _ = _pdf_init((148, 210))
    W, M = 148, 6; CW = W - 2 * M

    def cell(x, y, w, h, text, align='R', border=1, fill=False, size=8, color=(0, 0, 0)):
        pdf.set_xy(x, y); pdf.set_font("F", size=size); pdf.set_text_color(*color)
        pdf.cell(w, h, rtl(text), border=border, align=align, fill=fill)

    for s in slips:
        pay, emp, dept, dets = s['pay'], s['emp'], s['dept'], s['details']
        if not emp: continue
        pdf.add_page()
        pdf.set_fill_color(30, 58, 95); pdf.rect(M, 6, CW, 22, 'F')
        _draw_logo(pdf, (company.get('logo') or ''), M + 2, 8, 18, 18)
        cell(M + 22, 8, CW - 24, 8, company.get('name') or APP_TITLE, 'R', 0, False, 13, (240, 180, 41))
        cell(M + 22, 15, CW - 24, 6, f"{company.get('address') or ''} | {company.get('phone') or ''}",
             'R', 0, False, 7, (255, 255, 255))
        pdf.set_fill_color(240, 180, 41)
        cell(M, 30, CW, 8, f"فیش حقوقی — {MONTHS[pay['month']-1]} {pay['year']}",
             'C', 0, True, 12, (30, 58, 95))
        y = 41
        info = [("کد", emp.get('personnel_code') or emp['id']),
                ("نام", f"{emp.get('first_name','')} {emp.get('last_name','')}"),
                ("کد ملی", emp.get('national_code') or '-'),
                ("دپارتمان", (dept or {}).get('title', '-')),
                ("سمت", emp.get('job_title') or '-'),
                ("استخدام", emp.get('employment_date') or '-'),
                ("بیمه", emp.get('insurance_number') or '-'),
                ("حساب", emp.get('account_number') or '-'),
                ("روز", f"{pay['work_days']:g}"),
                ("اضافه‌کاری", hours_to_hm(pay.get('overtime_hours') or 0))]
        half = CW / 2
        for i in range(0, len(info), 2):
            for j in range(2):
                if i + j < len(info):
                    k, v = info[i + j]
                    cell(M + (1 - j) * half, y, half, 6, f"{k}: {v}", 'R', 1, False, 8)
            y += 6
        y += 2

        def sec(title, rows, y, color):
            pdf.set_fill_color(*color)
            cell(M, y, CW, 6, title, 'C', 1, True, 9, (255, 255, 255))
            y += 6
            for name, amt in rows:
                cell(M + CW * 0.4, y, CW * 0.6, 5.5, name, 'R', 1, False, 8)
                cell(M, y, CW * 0.4, 5.5, fmt(amt), 'L', 1, False, 8)
                y += 5.5
            return y + 1

        gross = [("حقوق پایه", pay['base_salary_monthly'])] + \
                [(d['name'], d['amount']) for d in dets if d['type'] == 1 and d['amount'] > 0]
        y = sec("حقوق و مزایا", gross, y, (28, 78, 111))
        extras = []
        for n, k in (("اضافه‌کاری", 'overtime_amount'), ("نوبت‌کاری", 'shift_amount'),
                     ("شب‌کاری", 'night_amount'), ("ماموریت", 'mission_amount'),
                     ("جمعه‌کاری", 'friday_amount'), ("تعطیل‌کاری", 'holiday_amount')):
            v = pay.get(k, 0) or 0
            if v: extras.append((n, v))
        if extras: y = sec("اضافات", extras, y, (28, 78, 111))
        ded = [(d['name'], d['amount']) for d in dets if d['type'] == 2 and d['amount'] > 0]
        y = sec("کسورات", ded or [("-", 0)], y, (192, 57, 43))
        pdf.set_fill_color(255, 249, 239)
        cell(M, y, CW, 7, f"جمع ناخالص: {fmt(pay['gross_salary'])} ریال", 'R', 1, True, 10)
        y += 7
        pdf.set_fill_color(255, 241, 207)
        cell(M, y, CW, 10, f"خالص پرداختی: {fmt(pay['net_salary'])} ریال",
             'R', 1, True, 13, (192, 57, 43))
        y += 14
        cell(M, y, CW, 5, f"{DEVELOPER} — {DEVELOPER_PHONE}", 'C', 0, False, 7, (100, 100, 100))
    pdf.output(path)
    return path

def build_payroll_list_pdf(path, company, year, month, rows):
    """لیست حقوق و دستمزد A4 افقی — چیدمان راست‌به‌چپ استاندارد ایران."""
    pdf, _ = _pdf_init((297, 210))
    W, M = 297, 6
    pdf.add_page()
    pdf.set_fill_color(30, 58, 95); pdf.rect(M, 6, W - 2*M, 12, 'F')
    pdf.set_xy(M, 8); pdf.set_font("F", size=13); pdf.set_text_color(240, 180, 41)
    pdf.cell(W - 2*M, 8, rtl(f"لیست حقوق و دستمزد — {MONTHS[month-1]} {year}"), border=0, align='C')
    pdf.set_xy(M, 20); pdf.set_font("F", size=9); pdf.set_text_color(0, 0, 0)
    pdf.cell(W - 2*M, 6, rtl(f"شرکت: {company.get('name','')}"), border=0, align='R')
    y = 28

    # 🆕 چیدمان ستون‌ها از راست به چپ (ایندکس ۰ = سمت راست)
    headers = ["#", "نام", "پایه", "اضافه", "شب", "نوبت", "جمعه", "مزایا",
               "ناخالص", "بیمه", "مالیات", "وام", "کسر", "خالص"]
    headers_rtl = list(reversed(headers))
    col_w = [(W - 2*M) / len(headers_rtl)] * len(headers_rtl)

    pdf.set_fill_color(240, 180, 41); pdf.set_text_color(30, 58, 95); pdf.set_font("F", size=8)
    x = M
    for i, h in enumerate(headers_rtl):
        pdf.set_xy(x, y); pdf.cell(col_w[i], 6, rtl(h), border=1, align='C', fill=True)
        x += col_w[i]
    y += 6

    pdf.set_text_color(0, 0, 0); pdf.set_font("F", size=7)
    total_gross = total_net = 0
    for idx, r in enumerate(rows, 1):
        if y > 190:
            pdf.add_page(); y = 20
        vals = [str(idx), f"{r['first_name']} {r['last_name']}",
                fmt(r['base_salary_monthly']), fmt(r.get('overtime_amount', 0)),
                fmt(r.get('night_amount', 0)), fmt(r.get('shift_amount', 0)),
                fmt(r.get('friday_amount', 0)), fmt(r.get('benefits_sum', 0)),
                fmt(r['gross_salary']), fmt(r['insurance_emp']), fmt(r['tax']),
                fmt(r['loan_install']), fmt(r['absent_ded']), fmt(r['net_salary'])]
        vals_rtl = list(reversed(vals))          # 🆕
        x = M
        for i, v in enumerate(vals_rtl):
            pdf.set_xy(x, y); pdf.cell(col_w[i], 5.5, rtl(v), border=1, align='C')
            x += col_w[i]
        y += 5.5
        total_gross += r['gross_salary']; total_net += r['net_salary']

    pdf.set_fill_color(240, 180, 41); pdf.set_text_color(30, 58, 95); pdf.set_font("F", size=8)
    pdf.set_xy(M, y)
    pdf.cell(W - 2*M, 7, rtl(f"جمع کل: ناخالص {fmt(total_gross)} — خالص {fmt(total_net)}"),
             border=1, align='C', fill=True)
    pdf.output(path)
    return path
# ═══════════════════════════════════════════════════════════════════════════
#           کلاس جامع قرارداد کار — جایگزین کامل بخش قرارداد در برنامه
#           توسعه‌دهنده: عرفان بلوچ | سیستم: عرفان حساب
# ═══════════════════════════════════════════════════════════════════════════
class Contract:
    """موتور کامل مدیریت، ویرایش و رندر قرارداد کار.

    این کلاس تمام جنبه‌های قرارداد را پوشش می‌دهد:
      ▸ قالب پیش‌فرض رسمی با ۹ ماده قانونی مطابق قانون کار ایران
      ▸ تجزیه‌گر مارکرهای ساختاری (#T #C #L #R #P #S #A #BOX #TBL #HR)
      ▸ جانشینی خودکار متغیرها {{name}} از داده‌های شرکت/پرسنل
      ▸ اعتبارسنجی متغیرهای ناشناخته
      ▸ پیش‌نمایش متنی قبل از تولید PDF
      ▸ رندر PDF حرفه‌ای: حاشیه دوگانه، هدر لوگو، جدول، کارت امضا، فوتر
      ▸ دیالوگ UI کامل با چیپ‌های متغیر/مارکر و پیش‌نمایش زنده
      ▸ ذخیره/بازگردانی قالب اختصاصی شرکت

    طریقه استفاده
    -------------
        Contract(app, emp).open()          # نمایش دیالوگ قرارداد
        Contract(app).open()               # نمایش دیالوگ قالب عمومی
    """

    # ─────────────────────── ثابت‌های ساختاری ───────────────────────
    PAGE_SIZE = (210, 297)              # A4 عمودی
    MARGIN    = 12
    FOOTER_H  = 15

    # ─────────────────────── پالت رنگی حرفه‌ای ───────────────────────
    C_PRIMARY       = (30, 58, 95)      # نیلی اصلی
    C_PRIMARY_LIGHT = (45, 90, 140)     # نیلی روشن
    C_PRIMARY_DARK  = (15, 36, 64)      # نیلی تیره
    C_ACCENT        = (240, 180, 41)    # طلایی اصلی
    C_ACCENT_SOFT   = (255, 241, 207)   # طلایی کرم
    C_ACCENT_DARK   = (200, 145, 20)    # طلایی تیره
    C_LINE          = (200, 210, 225)   # خط جدول
    C_LINE_SOFT     = (228, 233, 240)   # خط ضعیف
    C_TEXT          = (15, 23, 42)      # متن اصلی
    C_MUTED         = (100, 116, 139)   # متن کم‌رنگ
    C_WHITE         = (255, 255, 255)
    C_SOFT          = (238, 242, 247)   # پس‌زمینه ملایم
    C_SOFT_ALT      = (249, 251, 253)   # پس‌زمینه جایگزین
    C_DANGER        = (192, 57, 43)
    C_SUCCESS       = (16, 185, 129)

    # ─────────────────────── قالب پیش‌فرض رسمی ───────────────────────
    DEFAULT_TEMPLATE = """#T قرارداد کار
#C مطابق ماده ۷ قانون کار جمهوری اسلامی ایران

#P این قرارداد فی‌مابین شرکت «{{company_name}}» به شماره ثبت {{company_reg}} و کد اقتصادی {{company_economic}}، به نشانی {{company_address}}، تلفن {{company_phone}}، به نمایندگی «{{company_manager}}» (که از این پس «کارفرما» نامیده می‌شود) از یک طرف؛ و آقای/خانم «{{first_name}} {{last_name}}» فرزند {{father_name}}، به کد ملی {{national_code}}، شماره شناسنامه {{id_number}}، صادره از {{id_issue_place}}، متولد {{birth_date}} در {{birth_place}}، ساکن {{address}}، تلفن همراه {{mobile}} (که از این پس «کارگر» نامیده می‌شود) از طرف دیگر؛ با استناد به ماده ۷ قانون کار جمهوری اسلامی ایران و رعایت کلیه مقررات جاری، منعقد می‌گردد.

#S مشخصات کارگر
#TBL
نام و نام خانوادگی|{{first_name}} {{last_name}}|نام پدر|{{father_name}}
کد ملی|{{national_code}}|شماره شناسنامه|{{id_number}}
محل صدور|{{id_issue_place}}|تاریخ تولد|{{birth_date}}
محل تولد|{{birth_place}}|تلفن همراه|{{mobile}}
سمت سازمانی|{{job_title}}|واحد سازمانی|{{dept_title}}
تاریخ استخدام|{{employment_date}}|پایان قرارداد|{{contract_end}}
شماره بیمه|{{insurance_number}}|کد مالیاتی|{{tax_file_code}}
#/TBL

#S حقوق و مزایا
#TBL
حقوق روزانه|{{daily_salary}} ریال|حقوق ماهانه|{{monthly_salary}} ریال
ساعت کار هفتگی|۴۴ ساعت طبق ماده ۵۱|ساعت کار روزانه|{{work_start}} تا {{work_end}}
#/TBL

#A ماده ۱ — موضوع قرارداد
#P انجام وظایف مربوط به سمت «{{job_title}}» در واحد سازمانی «{{dept_title}}» طبق شرح وظایف و ضوابط کارفرما.

#A ماده ۲ — مدت قرارداد
#P از تاریخ {{employment_date}} لغایت {{contract_end}}.

#A ماده ۳ — محل انجام کار
#P {{company_address}} یا هر محلی که کارفرما حسب مقتضیات تعیین نماید.

#A ماده ۴ — ساعات کار
#P طبق ماده ۵۱ قانون کار، ۴۴ ساعت در هفته؛ از ساعت {{work_start}} تا {{work_end}}.

#A ماده ۵ — حقوق و مزایا
#P حقوق روزانه {{daily_salary}} ریال معادل ماهانه {{monthly_salary}} ریال، به‌علاوه مزایای قانونی (حق مسکن، بن کارگری، حق تاهل، حق اولاد و ...).

#A ماده ۶ — بیمه
#P کارگر از بدو اشتغال تحت پوشش سازمان تأمین اجتماعی قرار می‌گیرد. شماره بیمه: {{insurance_number}}.

#A ماده ۷ — تعطیلات و مرخصی
#P طبق مواد ۶۴ تا ۷۳ قانون کار جمهوری اسلامی ایران.

#A ماده ۸ — فسخ قرارداد
#P طبق مواد ۲۴ تا ۲۷ و ۴۱ قانون کار جمهوری اسلامی ایران.

#A ماده ۹ — نسخ قرارداد
#P این قرارداد در ۹ ماده و دو نسخه تنظیم و هر نسخه حکم واحد دارد.

#BOX کارفرما متعهد می‌گردد کلیه حقوق قانونی کارگر را طبق قانون کار و تأمین اجتماعی در موعد مقرر پرداخت نماید.

#C تاریخ انعقاد: {{today}}
"""

    # ─────────────────── گروه‌بندی متغیرها (UI) ───────────────────
    VARIABLE_GROUPS = (
        ("🏢 شرکت", (
            ("company_name",       "نام شرکت"),
            ("company_reg",        "شماره ثبت"),
            ("company_economic",   "کد اقتصادی"),
            ("company_address",    "آدرس شرکت"),
            ("company_phone",      "تلفن شرکت"),
            ("company_manager",    "مدیرعامل"),
            ("company_accountant", "حسابدار"),
        )),
        ("⏰ ساعت کار", (
            ("work_start", "ساعت شروع"),
            ("work_end",   "ساعت پایان"),
            ("today",      "تاریخ امروز"),
        )),
        ("🪪 هویت کارگر", (
            ("first_name",     "نام"),
            ("last_name",      "نام خانوادگی"),
            ("father_name",    "نام پدر"),
            ("national_code",  "کد ملی"),
            ("id_number",      "شماره شناسنامه"),
            ("id_issue_place", "محل صدور"),
            ("birth_date",     "تاریخ تولد"),
            ("birth_place",    "محل تولد"),
            ("address",        "آدرس"),
            ("mobile",         "تلفن همراه"),
            ("phone",          "تلفن ثابت"),
        )),
        ("💼 اطلاعات شغلی", (
            ("job_title",       "عنوان شغلی"),
            ("dept_title",      "واحد سازمانی"),
            ("employment_date", "تاریخ استخدام"),
            ("contract_end",    "پایان قرارداد"),
        )),
        ("💰 حقوق و بیمه", (
            ("daily_salary",     "حقوق روزانه"),
            ("monthly_salary",   "حقوق ماهانه"),
            ("insurance_number", "شماره بیمه"),
            ("tax_file_code",    "کد پرونده مالیاتی"),
        )),
    )

    # ────────────── راهنمای مارکرها (UI) ──────────────
    # (کد, برچسب, نمونه درج, رنگ‌کلید, رنگ‌متن)
    MARKER_HELP = (
        ("#T",   "عنوان وسط طلایی",       "#T عنوان سند\n",       "primary", "white"),
        ("#S",   "سرتیتر بخش نیلی",        "#S بخش جدید\n",        "primary", "white"),
        ("#A",   "عنوان ماده آبی",         "#A ماده ۱ — موضوع\n",  "primary", "white"),
        ("#C",   "پاراگراف وسط‌چین",       "#C متن وسط\n",         "info",    "primary"),
        ("#R",   "پاراگراف راست‌چین",      "#R متن راست\n",        "success", "primary"),
        ("#L",   "پاراگراف چپ‌چین",        "#L متن چپ\n",          "warning", "primary"),
        ("#P",   "پاراگراف پیش‌فرض",       "#P متن پاراگراف\n",    "success", "primary"),
        ("#BOX", "کادر متنی طلایی",        "#BOX متن کادر\n",      "accent",  "primary"),
        ("#HR",  "خط جداکننده افقی",        "#HR\n",                "muted",   "white"),
        ("#TBL", "جدول (سلول‌ها با |)",     "#TBL\nعنوان|مقدار\n#/TBL\n", "purple", "primary"),
    )

    # ═══════════════════════════════════════════════════════════════════
    #                            سازنده
    # ═══════════════════════════════════════════════════════════════════
    def __init__(self, app, emp=None):
        """
        Parameters
        ----------
        app : App
            نمونه کلاس اصلی برنامه (برای دسترسی به db/page/dialog...)
        emp : dict یا None
            اطلاعات پرسنل. اگر None باشد، دیالوگ قالب عمومی باز می‌شود.
        """
        self.app     = app
        self.db      = app.db
        self.page    = app.page
        self.cid     = app.cid
        self.emp     = emp
        self.company = self.db.q1("SELECT * FROM companies WHERE id=?", (self.cid,)) or {}
        self.depts   = {d['id']: d for d in
                        self.db.q("SELECT * FROM departments WHERE company_id=?", (self.cid,))}
        self.dept    = self.depts.get((emp or {}).get('dept_id'))
        self.template = (self.company.get('contract_template')
                         or self.DEFAULT_TEMPLATE)

        # رفرنس‌های PDF (در حین رندر مقداردهی می‌شوند)
        self._pdf    = None
        self._ctx    = {}
        self._page_w = self.PAGE_SIZE[0]
        self._page_h = self.PAGE_SIZE[1]
        self._cw     = self._page_w - 2 * self.MARGIN
        self._cw_in  = self._cw - 4

    # ═══════════════════════════════════════════════════════════════════
    #                   ۱) ابزارهای استاتیک (بدون وابستگی)
    # ═══════════════════════════════════════════════════════════════════
    @staticmethod
    def parse(text):
        """متن قالب → لیست بلوک‌های (نوع, محتوا)."""
        if not text:
            return []
        blocks = []
        lines  = text.split('\n')
        i = 0
        while i < len(lines):
            s = lines[i].strip()
            if not s:
                i += 1; continue

            # جدول چندخطی
            if s == '#TBL':
                rows = []; i += 1
                while i < len(lines) and lines[i].strip() != '#/TBL':
                    r = lines[i].strip()
                    if r:
                        rows.append([c.strip() for c in r.split('|')])
                    i += 1
                if rows:
                    blocks.append(('table', rows))
                i += 1; continue

            if   s.startswith('#T '):   blocks.append(('title',   s[3:].strip()))
            elif s.startswith('#C '):   blocks.append(('para',    (s[3:].strip(), 'C')))
            elif s.startswith('#L '):   blocks.append(('para',    (s[3:].strip(), 'L')))
            elif s.startswith('#R '):   blocks.append(('para',    (s[3:].strip(), 'R')))
            elif s.startswith('#P '):   blocks.append(('para',    (s[3:].strip(), 'R')))
            elif s.startswith('#S '):   blocks.append(('section', s[3:].strip()))
            elif s.startswith('#A '):   blocks.append(('article', s[3:].strip()))
            elif s.startswith('#BOX '): blocks.append(('box',     s[5:].strip()))
            elif s == '#HR':            blocks.append(('hr',      None))
            else:                       blocks.append(('para',    (s, 'R')))
            i += 1
        return blocks

    @classmethod
    def extract_variables(cls, text):
        return set(re.findall(r'\{\{\s*(\w+)\s*\}\}', text or ''))

    @classmethod
    def known_variables(cls):
        return {name for _, items in cls.VARIABLE_GROUPS for name, _ in items}

    @classmethod
    def validate_template(cls, text):
        unknown = cls.extract_variables(text) - cls.known_variables()
        return (len(unknown) == 0, unknown)

    # ═══════════════════════════════════════════════════════════════════
    #                   ۲) ساخت Context از داده‌ها
    # ═══════════════════════════════════════════════════════════════════
    def _build_context(self):
        """دیکشنری مقدار متغیرها از داده‌های شرکت + پرسنل."""
        c = self.company or {}
        e = self.emp or {}

        def g(d, k, default='—'):
            v = d.get(k)
            if v in (None, '', 0):
                return default
            return v

        return {
            'company_name':       g(c, 'name', APP_TITLE),
            'company_reg':        g(c, 'reg_no'),
            'company_economic':   g(c, 'economic_code'),
            'company_address':    g(c, 'address'),
            'company_phone':      g(c, 'phone'),
            'company_manager':    g(c, 'sign_manager'),
            'company_accountant': g(c, 'sign_accountant'),
            'work_start':         g(c, 'default_work_start', '08:00'),
            'work_end':           g(c, 'default_work_end',   '16:00'),
            'today':              jalali_today_str(),
            'first_name':         g(e, 'first_name'),
            'last_name':          g(e, 'last_name'),
            'father_name':        g(e, 'father_name'),
            'national_code':      g(e, 'national_code'),
            'id_number':          g(e, 'id_number'),
            'id_issue_place':     g(e, 'id_issue_place'),
            'birth_date':         g(e, 'birth_date'),
            'birth_place':        g(e, 'birth_place'),
            'address':            g(e, 'address'),
            'mobile':             g(e, 'mobile'),
            'phone':              g(e, 'phone'),
            'job_title':          g(e, 'job_title'),
            'dept_title':         (self.dept or {}).get('title') or '—',
            'employment_date':    g(e, 'employment_date'),
            'contract_end':       g(e, 'contract_end'),
            'daily_salary':       fmt(e.get('daily_salary') or 0),
            'monthly_salary':     fmt((e.get('daily_salary') or 0) * 30),
            'insurance_number':   g(e, 'insurance_number'),
            'tax_file_code':      g(e, 'tax_file_code'),
        }

    def _render_text(self, template):
        """جایگزینی متغیرها در متن قالب."""
        out = template or self.DEFAULT_TEMPLATE
        ctx = self._build_context()
        for k, v in ctx.items():
            out = out.replace("{{" + k + "}}", str(v))
        # پاکسازی متغیرهای ناشناخته باقیمانده
        out = re.sub(r'\{\{\s*\w+\s*\}\}', '—', out)
        return out

    @classmethod
    def preview_text(cls, template, company, emp, dept_title=''):
        """متن پیش‌نمایش با حذف مارکرها (برای نمایش در دیالوگ)."""
        # ساخت context موقت
        c, e = company or {}, emp or {}

        def g(d, k, default='—'):
            v = d.get(k)
            return default if v in (None, '', 0) else v

        ctx = {
            'company_name':   g(c, 'name', APP_TITLE),
            'company_reg':    g(c, 'reg_no'),
            'company_economic': g(c, 'economic_code'),
            'company_address': g(c, 'address'),
            'company_phone':  g(c, 'phone'),
            'company_manager': g(c, 'sign_manager'),
            'company_accountant': g(c, 'sign_accountant'),
            'work_start':     g(c, 'default_work_start', '08:00'),
            'work_end':       g(c, 'default_work_end',   '16:00'),
            'today':          jalali_today_str(),
            'first_name':     g(e, 'first_name'),
            'last_name':      g(e, 'last_name'),
            'father_name':    g(e, 'father_name'),
            'national_code':  g(e, 'national_code'),
            'id_number':      g(e, 'id_number'),
            'id_issue_place': g(e, 'id_issue_place'),
            'birth_date':     g(e, 'birth_date'),
            'birth_place':    g(e, 'birth_place'),
            'address':        g(e, 'address'),
            'mobile':         g(e, 'mobile'),
            'phone':          g(e, 'phone'),
            'job_title':      g(e, 'job_title'),
            'dept_title':     dept_title or '—',
            'employment_date': g(e, 'employment_date'),
            'contract_end':   g(e, 'contract_end'),
            'daily_salary':   fmt(e.get('daily_salary') or 0),
            'monthly_salary': fmt((e.get('daily_salary') or 0) * 30),
            'insurance_number': g(e, 'insurance_number'),
            'tax_file_code':  g(e, 'tax_file_code'),
        }
        out = template or cls.DEFAULT_TEMPLATE
        for k, v in ctx.items():
            out = out.replace("{{" + k + "}}", str(v))
        out = re.sub(r'\{\{\s*\w+\s*\}\}', '—', out)

        # حذف مارکرها برای نمایش تمیز
        result = []
        for line in out.split('\n'):
            s = line.strip()
            if not s:
                result.append('')
                continue
            if s == '#HR':
                result.append('─' * 40)
            elif s in ('#TBL', '#/TBL'):
                continue
            elif s.startswith(('#T ', '#S ', '#A ', '#C ', '#L ', '#R ', '#P ', '#BOX ')):
                result.append(s.split(' ', 1)[1])
            elif '|' in s:
                result.append('  |  '.join(c.strip() for c in s.split('|')))
            else:
                result.append(s)
        return '\n'.join(result)

    # ═══════════════════════════════════════════════════════════════════
    #                   ۳) رندر PDF
    # ═══════════════════════════════════════════════════════════════════
        # ═══════════════════════════════════════════════════════════════════
    #                   ۳) رندر PDF کلاسیک و حرفه‌ای
    # ═══════════════════════════════════════════════════════════════════
    def render_pdf(self, path, template=None):
        """PDF قرارداد — برگه سفید، قاب دور برگه، هدر لوگو، امضاها."""
        pdf, _ = _pdf_init(self.PAGE_SIZE)
        self._pdf = pdf
        self._ctx = self._build_context()

        text = self._render_text(template or self.template)
        blocks = self.parse(text)

        pdf.add_page()
        self._draw_border()
        y = self._draw_header()

        for kind, content in blocks:
            y = self._dispatch(kind, y, content)

        # اطمینان از فضای کافی برای تاریخ و امضا
        y = self._ensure(y, 55)
        y += 3
        y = self._draw_signatures(y)

        self._draw_footer(pdf.page_no())
        pdf.output(path)
        return path

    def _dispatch(self, kind, y, content):
        if   kind == 'title':   return self._r_title(y, content)
        elif kind == 'section': return self._r_section(y, content)
        elif kind == 'article': return self._r_article(y, content)
        elif kind == 'para':
            text, align = content
            return self._r_para(y, text, align)
        elif kind == 'box':     return self._r_box(y, content)
        elif kind == 'hr':      return self._r_hr(y)
        elif kind == 'table':   return self._r_table(y, content)
        return y

    # ── عنوان اصلی (نوار نیلی + طلایی) ──
    def _r_title(self, y, text):
        h = 14
        y = self._ensure(y, h + 6)
        pdf = self._pdf
        # نوار نیلی
        pdf.set_fill_color(*self.C_PRIMARY)
        pdf.rect(self.MARGIN + 2, y, self._cw_in, h, 'F')
        # خط طلایی زیر نوار
        pdf.set_fill_color(*self.C_ACCENT)
        pdf.rect(self.MARGIN + 2, y + h, self._cw_in, 0.7, 'F')
        # متن طلایی
        self._sf(16, (255, 220, 130))
        pdf.set_xy(self.MARGIN + 2, y + 3)
        pdf.cell(self._cw_in, 8, rtl(text), border=0, align='C')
        return y + h + 4.5

    # ── سرتیتر بخش (نوار طلایی روشن) ──
    def _r_section(self, y, text):
        y = self._ensure(y, 12)
        h = 8
        pdf = self._pdf
        # پس‌زمینه کرم طلایی
        pdf.set_fill_color(255, 248, 220)
        pdf.rect(self.MARGIN + 2, y, self._cw_in, h, 'F')
        # قاب طلایی
        pdf.set_draw_color(*self.C_ACCENT)
        pdf.set_line_width(0.4)
        pdf.rect(self.MARGIN + 2, y, self._cw_in, h, 'D')
        # نوار طلایی سمت راست
        pdf.set_fill_color(*self.C_ACCENT)
        pdf.rect(self.MARGIN + self._cw_in - 1.5, y, 1.5, h, 'F')
        # متن
        self._sf(11, self.C_PRIMARY)
        pdf.set_xy(self.MARGIN + 2, y + 1.5)
        pdf.cell(self._cw_in, 5, rtl(text), border=0, align='C')
        return y + h + 3

    # ── عنوان ماده (نوار نیلی ملایم) ──
    def _r_article(self, y, text):
        y = self._ensure(y, 14)
        h = 7.5
        pdf = self._pdf
        # پس‌زمینه نیلی ملایم
        pdf.set_fill_color(*self.C_SOFT)
        pdf.rect(self.MARGIN + 2, y, self._cw_in, h, 'F')
        # قاب نیلی
        pdf.set_draw_color(*self.C_PRIMARY)
        pdf.set_line_width(0.35)
        pdf.rect(self.MARGIN + 2, y, self._cw_in, h, 'D')
        # نوار نیلی سمت راست
        pdf.set_fill_color(*self.C_PRIMARY)
        pdf.rect(self.MARGIN + self._cw_in - 1.8, y, 1.8, h, 'F')
        # متن
        self._sf(10, self.C_PRIMARY)
        pdf.set_xy(self.MARGIN + 3, y + 1)
        pdf.cell(self._cw_in - 2, 5, rtl(text), border=0, align='R')
        return y + h + 1.5

    # ── پاراگراف ──
    def _r_para(self, y, text, align='R'):
        pdf = self._pdf
        pad_x, line_h = 3, 5.8
        width = self._cw_in - 2 * pad_x
        size = 9.5

        lines = self._wrap_rtl(text, width, size)
        if not lines:
            return y + line_h

        y = self._ensure(y, len(lines) * line_h + 2)
        self._sf(size, self.C_TEXT)

        for line in lines:
            pdf.set_xy(self.MARGIN + 2 + pad_x, y)
            pdf.cell(width, line_h, rtl(line), border=0, align=align)
            y += line_h

        return y + 1.5

    def _wrap_rtl(self, text, max_width_mm, size):
        """شکست متن فارسی به خطوط با در نظر گرفتن RTL و عرض واقعی."""
        pdf = self._pdf
        pdf.set_font("F", size=size)

        words = str(text).split()
        if not words:
            return []

        space_w = pdf.get_string_width(' ')
        lines, current, current_w = [], [], 0.0

        for w in words:
            display_w = pdf.get_string_width(rtl(w))
            if current and current_w + space_w + display_w > max_width_mm:
                lines.append(' '.join(current))
                current, current_w = [w], display_w
            else:
                if current:
                    current_w += space_w + display_w
                else:
                    current_w = display_w
                current.append(w)

        if current:
            lines.append(' '.join(current))
        return lines

    # ── کادر طلایی (متن برجسته) ──
    def _r_box(self, y, text):
        pdf = self._pdf
        pad, line_h = 4, 5.8
        inner_w = self._cw_in - 10
        size = 9.3

        lines = self._wrap_rtl(text, inner_w, size)
        if not lines:
            return y + line_h

        box_h = len(lines) * line_h + 2 * pad
        y = self._ensure(y, box_h + 3)

        # پس‌زمینه کرم
        pdf.set_fill_color(255, 248, 220)
        pdf.rect(self.MARGIN + 2, y, self._cw_in, box_h, 'F')
        # قاب طلایی
        pdf.set_draw_color(*self.C_ACCENT)
        pdf.set_line_width(0.5)
        pdf.rect(self.MARGIN + 2, y, self._cw_in, box_h, 'D')
        # نوار طلایی سمت راست
        pdf.set_fill_color(*self.C_ACCENT)
        pdf.rect(self.MARGIN + self._cw_in - 2.5, y, 2.5, box_h, 'F')

        self._sf(size, self.C_TEXT)
        yy = y + pad
        for line in lines:
            pdf.set_xy(self.MARGIN + 6, yy)
            pdf.cell(inner_w, line_h, rtl(line), border=0, align='R')
            yy += line_h

        return y + box_h + 3

    # ── خط جداکننده ──
    def _r_hr(self, y):
        y = self._ensure(y, 6)
        pdf = self._pdf
        pdf.set_draw_color(*self.C_ACCENT)
        pdf.set_line_width(0.35)
        pdf.line(self.MARGIN + 8, y + 3, self._page_w - self.MARGIN - 8, y + 3)
        return y + 6

    # ── جدول نرم و کلاسیک ──
    def _r_table(self, y, rows):
        if not rows:
            return y
        ncols = max(len(r) for r in rows)
        col_w = self._cw_in / ncols
        row_h = 7.2
        pdf = self._pdf

        for i, row in enumerate(rows):
            # شکست صفحه
            if y + row_h > self._page_h - self.FOOTER_H - 8:
                self._draw_footer(pdf.page_no())
                pdf.add_page()
                self._draw_border()
                y = self._draw_continuation_header()

            # راه‌راه ملایم
            bg = (248, 250, 253) if i % 2 == 0 else (255, 255, 255)
            pdf.set_fill_color(*bg)
            pdf.rect(self.MARGIN + 2, y, self._cw_in, row_h, 'F')
            pdf.set_draw_color(95, 115, 140)
            pdf.set_line_width(0.3)
            pdf.rect(self.MARGIN + 2, y, self._cw_in, row_h, 'D')

            # خطوط عمودی جداکننده (مستقل از RTL)
            for j in range(1, ncols):
                x = self.MARGIN + 2 + j * col_w
                pdf.set_draw_color(200, 210, 222)
                pdf.set_line_width(0.18)
                pdf.line(x, y + 1.5, x, y + row_h - 1.5)

            # 🆕 سلول‌ها: ایندکس ۰ در سمت راست رسم می‌شود (RTL)
            for j in range(ncols):
                cell = row[j] if j < len(row) else ''
                is_label = (ncols == 4 and j % 2 == 0) or (ncols == 2 and j == 0)
                if is_label:
                    self._sf(8.3, (60, 95, 140))
                else:
                    self._sf(8.7, (20, 30, 45))
                col_index = ncols - 1 - j          # 🆕 معکوس‌سازی موقعیت افقی
                pdf.set_xy(self.MARGIN + 2 + col_index * col_w + 2, y + 1.8)
                pdf.cell(col_w - 4, row_h - 3, rtl(cell), border=0, align='C')

            y += row_h
        return y + 3

    # ═══════════ عناصر صفحه ═══════════
    def _draw_border(self):
        """قاب دوگانه دور برگه — نیلی بیرون، طلایی درون."""
        pdf = self._pdf
        W, H = self._page_w, self._page_h
        # خط بیرونی نیلی پررنگ
        pdf.set_draw_color(55, 80, 110)
        pdf.set_line_width(0.6)
        pdf.rect(6, 6, W - 12, H - 12, 'D')
        # خط طلایی نازک داخلی
        pdf.set_draw_color(*self.C_ACCENT)
        pdf.set_line_width(0.25)
        pdf.rect(7.5, 7.5, W - 15, H - 15, 'D')

    def _draw_header(self):
        """هدر: نوار نیلی + لوگو + نام شرکت + اطلاعات تماس."""
        pdf = self._pdf
        W = self._page_w
        y0 = 11
        h = 20
        c = self.company or {}

        # نوار نیلی
        pdf.set_fill_color(*self.C_PRIMARY)
        pdf.rect(self.MARGIN, y0, self._cw, h, 'F')

        # لوگو گوشه راست
        _draw_logo(pdf, c.get('logo') or '',
                   W - self.MARGIN - 15, y0 + 2.5, 15, 15)

        # نام شرکت — طلایی روشن
        self._sf(13, (255, 220, 130))
        pdf.set_xy(self.MARGIN + 3, y0 + 3)
        pdf.cell(self._cw - 6, 7, rtl(c.get('name') or APP_TITLE),
                 border=0, align='C')

        # اطلاعات تماس
        info = []
        if c.get('reg_no'):         info.append(f"شناسه ملی: {c['reg_no']}")
        if c.get('economic_code'):  info.append(f"کد اقتصادی: {c['economic_code']}")
        if c.get('phone'):          info.append(f"تلفن: {c['phone']}")
        if c.get('address'):        info.append(c['address'])
        self._sf(7.2, (215, 225, 240))
        pdf.set_xy(self.MARGIN + 3, y0 + 11)
        pdf.cell(self._cw - 6, 5, rtl('   •   '.join(info) or '—'),
                 border=0, align='C')

        # خط طلایی زیر نوار
        pdf.set_fill_color(*self.C_ACCENT)
        pdf.rect(self.MARGIN, y0 + h, self._cw, 0.7, 'F')

        return y0 + h + 5

    def _draw_continuation_header(self):
        """هدر کوچک برای صفحات ادامه."""
        pdf = self._pdf
        c = self.company or {}
        y0 = 11
        h = 10
        pdf.set_fill_color(*self.C_PRIMARY)
        pdf.rect(self.MARGIN, y0, self._cw, h, 'F')
        self._sf(10, (255, 220, 130))
        pdf.set_xy(self.MARGIN + 3, y0 + 1)
        pdf.cell(self._cw - 6, 5, rtl(f"{c.get('name') or APP_TITLE}  —  ادامه قرارداد"),
                 border=0, align='C')
        self._sf(7, (215, 225, 240))
        pdf.set_xy(self.MARGIN + 3, y0 + 5.5)
        pdf.cell(self._cw - 6, 4, rtl("صفحه بعد"), border=0, align='C')
        pdf.set_fill_color(*self.C_ACCENT)
        pdf.rect(self.MARGIN, y0 + h, self._cw, 0.5, 'F')
        return y0 + h + 4

    def _draw_footer(self, page_no):
        """پانویس با خط طلایی و شماره صفحه."""
        pdf = self._pdf
        # خط طلایی
        pdf.set_draw_color(*self.C_ACCENT)
        pdf.set_line_width(0.3)
        pdf.line(self.MARGIN + 6, self._page_h - 15,
                 self._page_w - self.MARGIN - 6, self._page_h - 15)
        # متن
        self._sf(7.5, self.C_MUTED)
        pdf.set_xy(self.MARGIN, self._page_h - 13)
        pdf.cell(self._cw, 4,
                 rtl(f"صادر شده با {APP_TITLE}   •   {DEVELOPER}   •   {DEVELOPER_PHONE}"),
                 border=0, align='C')
        pdf.set_xy(self.MARGIN, self._page_h - 9)
        pdf.cell(self._cw, 4, rtl(f"صفحه {page_no}"), border=0, align='C')

    def _draw_signatures(self, y):
        """دو کادر امضا + تاریخ انعقاد."""
        pdf = self._pdf
        c = self.company or {}
        e = self.emp or {}

        # ─── نوار تاریخ انعقاد ───
        dh = 8
        pdf.set_fill_color(255, 248, 220)
        pdf.rect(self.MARGIN + 2, y, self._cw_in, dh, 'F')
        pdf.set_draw_color(*self.C_ACCENT)
        pdf.set_line_width(0.4)
        pdf.rect(self.MARGIN + 2, y, self._cw_in, dh, 'D')
        self._sf(10, self.C_PRIMARY)
        pdf.set_xy(self.MARGIN + 2, y + 1.5)
        pdf.cell(self._cw_in, 5,
                 rtl(f"تاریخ انعقاد قرارداد:   {self._ctx.get('today', jalali_today_str())}"),
                 border=0, align='C')
        y += dh + 5

        # ─── دو کادر امضا ───
        gap   = 6
        box_w = (self._cw_in - gap) / 2
        box_h = 34

        def sign_box(x, title, name, sub, color):
            # پس‌زمینه
            pdf.set_fill_color(248, 250, 253)
            pdf.rect(x, y, box_w, box_h, 'F')
            # نوار عنوان رنگی
            pdf.set_fill_color(*color)
            pdf.rect(x, y, box_w, 5.5, 'F')
            # متن نوار
            self._sf(9.5, (255, 255, 255))
            pdf.set_xy(x, y + 0.3)
            pdf.cell(box_w, 5, rtl(title), border=0, align='C')
            # قاب
            pdf.set_draw_color(*color)
            pdf.set_line_width(0.4)
            pdf.rect(x, y, box_w, box_h, 'D')
            # عنوان شغلی
            self._sf(8, self.C_MUTED)
            pdf.set_xy(x + 3, y + 7)
            pdf.cell(box_w - 6, 4, rtl(sub), border=0, align='C')
            # نام کامل
            self._sf(9, self.C_TEXT)
            pdf.set_xy(x, y + 12)
            pdf.cell(box_w, 5, rtl(name), border=0, align='C')
            # خط امضا (داخل کادر)
            pdf.set_draw_color(200, 210, 222)
            pdf.set_line_width(0.2)
            pdf.line(x + 10, y + 24, x + box_w - 10, y + 24)
            # برچسب
            self._sf(7.5, self.C_MUTED)
            pdf.set_xy(x, y + 26)
            pdf.cell(box_w, 4, rtl("امضاء / مهر"), border=0, align='C')

        # کادر کارفرما (راست)
        sign_box(
            self.MARGIN + 2 + box_w + gap,
            "کارفرما",
            c.get('name') or '—',
            f"مدیرعامل: {c.get('sign_manager') or '—'}",
            self.C_PRIMARY)

        # کادر کارگر (چپ)
        sign_box(
            self.MARGIN + 2,
            "کارگر",
            f"{e.get('first_name','')} {e.get('last_name','')}".strip() or '—',
            f"کد ملی: {e.get('national_code') or '—'}",
            self.C_ACCENT)

        return y + box_h + 4

    # ── کمکی ──
    def _sf(self, size=9.5, color=None):
        self._pdf.set_font("F", size=size)
        if color is not None:
            self._pdf.set_text_color(*color)

    def _ensure(self, y, need):
        if y + need <= self._page_h - self.FOOTER_H - 8:
            return y
        self._draw_footer(self._pdf.page_no())
        self._pdf.add_page()
        self._draw_border()
        return self._draw_continuation_header()

    # ═══════════════════════════════════════════════════════════════════
    #              ۴) دیالوگ UI — نقطه ورود اصلی
    # ═══════════════════════════════════════════════════════════════════
    def open(self):
        """دیالوگ ساده ویرایش + پیش‌نمایش + PDF."""
        editor = K(ft.TextField,
            value=self.template, multiline=True, text_size=11.5,
            text_align=ft.TextAlign.RIGHT,
            min_lines=22, max_lines=30, dense=False,
            content_padding=pad_sym(12, 12),
            border_color=T()['line'], border_radius=10,
            hint_text="متن قالب قرارداد...")

        # ─── درج متن در مکان نشانگر ───
        def insert_at_cursor(snippet):
            v = editor.value or ''
            if v and not v.endswith('\n'):
                v += '\n'
            editor.value = v + snippet
            try: editor.update()
            except Exception: pass
            refresh_status()

        # ─── چیپ قابل کلیک ───
        def chip(label, snippet, bg=None, fg=None):
            return ft.Container(
                content=txt(label, 10, True, fg or T()['primary']),
                bgcolor=bg or alpha(T()['accent'], 0x44),
                padding=pad_sym(9, 5), border_radius=14,
                on_click=lambda e, s=snippet: insert_at_cursor(s),
                ink=True)

        # ─── متغیرها و مارکرها ───
        cmap = {'primary': T()['primary'], 'accent': T()['accent'],
                'info': alpha(T()['info'], 0x66), 'success': alpha(T()['success'], 0x66),
                'warning': alpha(T()['warning'], 0x66), 'muted': T()['muted'],
                'purple': alpha(T()['purple'], 0x55)}
        fmap = {'white': '#ffffff', 'primary': T()['primary']}

        marker_chips = [chip(lbl, snip, cmap.get(bg, T()['accent']),
                             fmap.get(fg, T()['primary']))
                        for lbl, snip, bg, fg, *extra in self.MARKER_HELP]

        var_chips = []
        for group_title, items in self.VARIABLE_GROUPS:
            var_chips.append(ft.Container(
                content=ft.Column([
                    txt(group_title, 10, True, T()['primary']),
                    ft.Row([chip(lbl, "{{" + name + "}}") for name, lbl in items],
                           wrap=True, spacing=4, run_spacing=4),
                ], spacing=4, tight=True),
                padding=8, border_radius=8,
                bgcolor=alpha(T()['primary'], 0x06),
                border=border_all(1, T()['line'])))

        # ─── اعتبارسنجی زنده ───
        status = ft.Text("", size=10, color=T()['muted'])
        def refresh_status(e=None):
            ok, unknown = self.validate_template(editor.value or '')
            if not (editor.value or '').strip():
                status.value = "⚠️ قالب خالی است"
                status.color = T()['danger']
            elif ok:
                status.value = "✅ قالب معتبر"
                status.color = T()['success']
            else:
                status.value = f"⚠️ متغیر ناشناخته: {', '.join(sorted(unknown))}"
                status.color = T()['danger']
            try: status.update()
            except Exception: pass
        editor.on_change = refresh_status
        refresh_status()

        # ─── پیش‌نمایش ───
        def preview(e=None):
            try:
                pv = self.preview_text(editor.value or self.template,
                                       self.company, self.emp,
                                       (self.dept or {}).get('title', ''))
                d = ft.AlertDialog(
                    title=ft.Text("👁 پیش‌نمایش قالب", size=13),
                    content=ft.Container(
                        ft.Column([
                            ft.Container(
                                txt(pv, 10.5, selectable=True),
                                bgcolor='#ffffff', padding=14, border_radius=8,
                                border=border_all(1, T()['line'])),
                        ], scroll=ft.ScrollMode.AUTO, spacing=6, tight=True),
                        width=min((self.page.width or 400) - 40, 500),
                        height=min((self.page.height or 700) * 0.78, 620)),
                    actions=[tbtn("بستن", lambda ev: self.app.close_dlg(d))])
                self.app.open_dlg(d)
            except Exception as ex:
                self.app.toast(f"خطا: {ex}", True)

        # ─── ذخیره ───
        def do_save():
            self.db.update('companies', self.cid,
                           {'contract_template': editor.value or self.DEFAULT_TEMPLATE})
            self.app.toast("✅ قالب ذخیره شد")

        def save(ev):
            ok, unknown = self.validate_template(editor.value or '')
            if unknown:
                self.app.confirm(
                    "متغیر ناشناخته وجود دارد:\n" + "\n".join(sorted(unknown)) +
                    "\n\nبا این حال ذخیره شود؟",
                    do_save, "هشدار قالب")
                return
            do_save()

        # ─── بازگردانی پیش‌فرض ───
        def reset_default(ev):
            def go():
                editor.value = self.DEFAULT_TEMPLATE
                try: editor.update()
                except Exception: pass
                refresh_status()
                self.app.toast("🔄 قالب پیش‌فرض بارگذاری شد")
            self.app.confirm("قالب پیش‌فرض رسمی بارگذاری شود؟", go, "بازگردانی", False)

        # ─── چاپ PDF ───
        def print_pdf(ev):
            if not self.emp:
                self.app.toast("برای PDF ابتدا از پرسنل یک نفر را انتخاب کن", True)
                return
            try:
                path = os.path.join(
                    export_dir(),
                    f"contract_{self.emp['id']}_{datetime.now():%Y%m%d_%H%M%S}.pdf")
                self.render_pdf(path, editor.value or self.template)
                self.app.file_dialog(path, "📄 قرارداد PDF ساخته شد")
            except Exception as ex:
                log_error(traceback.format_exc())
                self.app.info("خطا در ساخت PDF", str(ex))

        # ─── عنوان دیالوگ ───
        if self.emp:
            title = (f"📄 قرارداد — {self.emp.get('first_name','')} "
                     f"{self.emp.get('last_name','')}")
        else:
            title = "📄 مدیریت قالب قرارداد"

        # ─── چیدمان نهایی ───
        dlg = ft.AlertDialog(
            modal=True,
            title=ft.Row([
                ft.Text(title, size=13, expand=True),
                status,
            ], vertical_alignment=ft.CrossAxisAlignment.CENTER),
            content=ft.Container(
                ft.Column([
                    # نوار مارکرها — یک ردیف فشرده
                    ft.Container(
                        content=ft.Column([
                            txt("🎯 چینش (کلیک = درج)", 10, True, T()['primary']),
                            ft.Row(marker_chips, wrap=True, spacing=4, run_spacing=4),
                        ], spacing=5, tight=True),
                        padding=8, border_radius=8,
                        bgcolor=T()['card'],
                        border=border_all(1, T()['accent'])),
                    # متغیرها — به‌صورت گروه‌های جمع‌وجور
                    ft.Container(
                        content=ft.Column([
                            txt("📌 متغیرها (کلیک = درج)", 10, True, T()['primary']),
                            *var_chips,
                        ], spacing=6, tight=True),
                        padding=8, border_radius=8,
                        bgcolor=T()['card'],
                        border=border_all(1, T()['line'])),
                    # ادیتور اصلی
                    txt("✍️ متن قالب", 10, True, T()['muted']),
                    editor,
                ], scroll=ft.ScrollMode.AUTO, spacing=8, tight=True),
                width=min((self.page.width or 400) - 20, 560),
                height=min((self.page.height or 700) * 0.85, 680)),
            actions=[
                tbtn("🔄 پیش‌فرض", reset_default),
                tbtn("👁 پیش‌نمایش", preview),
                tbtn("💾 ذخیره", save),
                gbtn("📄 PDF", _ic("PICTURE_AS_PDF"), print_pdf, T()['success'])
                    if self.emp else tbtn(""),
                tbtn("بستن", lambda e: self.app.close_dlg(dlg)),
            ])
        # حذف دکمه خالی
        dlg.actions = [a for a in dlg.actions
                       if not (hasattr(a, 'text') and a.text == "")]
        self.app.open_dlg(dlg)


# ═══════════════════════════════════════════════════════════════════════════
#               سازگاری با کد قدیمی — wrapper ها
# ═══════════════════════════════════════════════════════════════════════════
def build_contract_pdf(path, company, emp, template, dept_title=''):
    """wrapper برای سازگاری کدهای قدیمی که مستقیم این تابع را صدا می‌زنند."""
    c = Contract.__new__(Contract)
    c.app     = None
    c.db      = None
    c.page    = None
    c.cid     = None
    c.emp     = emp
    c.company = company
    c.dept    = {'title': dept_title}
    c.template = template or Contract.DEFAULT_TEMPLATE
    c._pdf = None
    c._ctx = {}
    c._page_w = Contract.PAGE_SIZE[0]
    c._page_h = Contract.PAGE_SIZE[1]
    c._cw     = c._page_w - 2 * Contract.MARGIN
    c._cw_in  = c._cw - 4
    return c.render_pdf(path, template)


# نگه‌داشتن نام سراسری برای سازگاری
DEFAULT_CONTRACT = Contract.DEFAULT_TEMPLATE
def build_contract_pdf(path, company, emp, template, dept_title=''):
    pdf, _ = _pdf_init((210, 297))
    W, M = 210, 15
    vars_map = {
        'company_name': company.get('name', ''), 'company_address': company.get('address', ''),
        'company_phone': company.get('phone', ''), 'company_manager': company.get('sign_manager', ''),
        'company_economic': company.get('economic_code', ''), 'company_reg': company.get('reg_no', ''),
        'first_name': emp.get('first_name', ''), 'last_name': emp.get('last_name', ''),
        'father_name': emp.get('father_name', ''), 'national_code': emp.get('national_code', ''),
        'id_number': emp.get('id_number', ''), 'id_issue_place': emp.get('id_issue_place', ''),
        'birth_date': emp.get('birth_date', ''), 'birth_place': emp.get('birth_place', ''),
        'address': emp.get('address', ''), 'mobile': emp.get('mobile', ''),
        'phone': emp.get('phone', ''), 'job_title': emp.get('job_title', ''),
        'dept_title': dept_title, 'employment_date': emp.get('employment_date', ''),
        'contract_end': emp.get('contract_end', ''),
        'daily_salary': fmt(emp.get('daily_salary', 0)),
        'monthly_salary': fmt((emp.get('daily_salary') or 0) * 30),
        'insurance_number': emp.get('insurance_number', ''),
        'work_start': company.get('default_work_start', '08:00'),
        'work_end': company.get('default_work_end', '16:00'),
        'today': jalali_today_str(),
    }
    text = template or DEFAULT_CONTRACT
    for k, v in vars_map.items():
        text = text.replace("{{" + k + "}}", str(v))

    pdf.add_page()
    pdf.set_fill_color(30, 58, 95); pdf.rect(M, 8, W - 2*M, 16, 'F')
    _draw_logo(pdf, (company.get('logo') or ''), M + 1, 9, 14, 14)
    pdf.set_xy(M + 18, 12); pdf.set_font("F", size=14); pdf.set_text_color(240, 180, 41)
    pdf.cell(W - 2*M - 18, 8, rtl(company.get('name') or APP_TITLE), border=0, align='R')
    y = 30
    pdf.set_text_color(0, 0, 0); pdf.set_font("F", size=11)
    for line in text.split('\n'):
        if y > 275: pdf.add_page(); y = 20
        pdf.set_xy(M, y)
        if line.strip() == '': y += 4; continue
        pdf.multi_cell(W - 2*M, 7, rtl(line), align='R')
        y = pdf.get_y() + 1
    pdf.output(path)
    return path
   
# ═══════════════════════ ابزارک‌های UI ═══════════════════════
def txt(s, size=12, bold=False, color=None, align=None, **kw):
    return K(ft.Text, value=str(s), size=size,
             weight=ft.FontWeight.BOLD if bold else None,
             color=color or T()['text'], text_align=align, **kw)

def card(content, padding=10, on_click=None, bgcolor=None, border_color=None,
         radius=14, shadow=True):
    kwargs = dict(content=content, padding=padding,
                  bgcolor=bgcolor or T()['card'], border_radius=radius,
                  on_click=on_click, border=border_all(1, border_color or T()['line']))
    if shadow:
        try:
            kwargs['shadow'] = ft.BoxShadow(blur_radius=8, spread_radius=0,
                                            color="#10000000", offset=ft.Offset(0, 2))
        except Exception: pass
    return K(ft.Container, **kwargs)

def badge(text, bg=None, fg=None, size=9):
    return ft.Container(txt(text, size, True, fg or T()['primary']),
                        bgcolor=bg or T()['accent'], border_radius=10,
                        padding=pad_sym(8, 3))

def _money_fmt(e):
    raw = ''.join(c for c in norm(e.control.value) if c.isdigit())
    new = f"{int(raw):,}" if raw else ""
    if new != e.control.value:
        e.control.value = new
        try: e.control.update()
        except Exception: pass

def tf(label, value="", kb=False, money=False, width=None, expand=False,
       on_change=None, hint=None, size=12, multiline=False, prefix=None,
       suffix=None, password=False, **kw):
    sval = "" if value in (None, "", "0", 0) else str(value)
    args = dict(label=label, value=sval, hint_text=hint,
                text_align=ft.TextAlign.RIGHT, text_size=size,
                label_style=ft.TextStyle(size=size - 1),
                content_padding=pad_sym(12, 12),
                width=width, expand=expand, dense=True, multiline=multiline,
                password=password, can_reveal_password=password,
                on_change=(lambda e: _money_fmt(e)) if money else on_change,
                prefix_icon=prefix, **_border_kwargs(10))
    if suffix: args['suffix_text'] = suffix
    if kb: args['keyboard_type'] = ft.KeyboardType.NUMBER
    args.update(kw)
    return K(ft.TextField, **args)

def dd(label, options, value=None, on_select=None, width=None, expand=False,
       size=12, hint=None):
    Opt = getattr(ft, "DropdownOption", None) or ft.dropdown.Option
    # مطمئن می‌شویم که value با یکی از key ها مطابقت دارد
    val_str = None if value is None else str(value)
    valid_keys = {str(k) for k, _ in options}
    if val_str is not None and val_str not in valid_keys:
        val_str = None
    args = dict(label=label, value=val_str,
                width=width, expand=expand, text_size=size,
                label_style=ft.TextStyle(size=size - 1),
                content_padding=pad_sym(12, 10), dense=True, hint_text=hint,
                options=[Opt(key=str(k), text=str(t)) for k, t in options],
                **_border_kwargs(10))
    if on_select:
        args['on_select' if 'on_select' in _params(ft.Dropdown) else 'on_change'] = on_select
    return K(ft.Dropdown, **args)

def _button(cls_name, text, icon, on_click, bg, fg, expand, height, width=None):
    cls = (getattr(ft, cls_name, None)
           or getattr(ft, "Button", None)
           or getattr(ft, "ElevatedButton", None)
           or getattr(ft, "TextButton", None))
    if cls is None:
        raise RuntimeError("هیچ کلاس دکمه‌ای در نسخه Flet پیدا نشد.")
    ps = _params(cls)
    style_kw = {}
    if fg: style_kw['color'] = fg
    if bg: style_kw['bgcolor'] = bg
    kw = dict(icon=icon, on_click=on_click, expand=expand, height=height, width=width,
              style=ft.ButtonStyle(**style_kw))
    if 'text' in ps: kw['text'] = text
    else: kw['content'] = text
    return K(cls, **kw)

def gbtn(text, icon, on_click, bg=None, fg="#ffffff", expand=False, height=40, size=12, width=None):
    return _button("ElevatedButton", text, icon, on_click, bg or T()['primary'], fg, expand, height, width)

def obtn(text, icon, on_click, expand=False, height=40, size=12):
    col = T()['accent'] if STATE['dark'] else T()['primary']
    return _button("OutlinedButton", text, icon, on_click, None, col, expand, height)

def tbtn(text, on_click, color=None):
    cls = getattr(ft, "TextButton")
    ps = _params(cls)
    kw = dict(on_click=on_click)
    if color: kw['style'] = ft.ButtonStyle(color=color)
    kw['text' if 'text' in ps else 'content'] = text
    return K(cls, **kw)

def wide(btn_factory):
    return ft.Row([btn_factory()], spacing=0)

def iconbtn(icon, on_click, color=None, size=22, tooltip=None):
    return K(ft.IconButton, icon=icon, icon_color=color, icon_size=size,
             tooltip=tooltip, on_click=on_click)

# ═══════════════════════ اپلیکیشن ═══════════════════════
class App:
    TABS = ["داشبورد", "پرسنل", "کارکرد", "حقوق", "بیشتر"]

    def __init__(self, page, db):
        self.page, self.db, self.svc = page, db, PayrollService(db)
        self.cid = db.active_company()
        self.year, self.month, _ = today_jalali()
        self.stack = []
        self.body = None
        self.appbar = None
        self.navbar = None
        self._defer = False
        self._queue = []
        self._kb_height = 0   # 🆕 نگهداری ارتفاع کیبورد
                # ساعت زنده
        self._clock_text = None
        self._clock_timer = None
        self._clock_stop = False

    def start(self):
        p = self.page
        p.title = APP_TITLE
        try: p.rtl = True
        except Exception: pass
        p.padding = 0
        try:
            font = os.path.join(HERE, "assets", "fonts", "Vazirmatn-Regular.ttf")
            if os.path.isfile(font):
                p.fonts = {"Vazir": "/fonts/Vazirmatn-Regular.ttf"}
                p.theme = ft.Theme(font_family="Vazir")
        except Exception: pass
        try: p.on_view_pop = lambda e: self.back()
        except Exception: pass
        # 🆕 ثبت رویداد تغییر ابعاد صفحه (باز/بسته شدن کیبورد)
        try: p.on_media_change = self.on_media_change
        except Exception: pass
        try: p.on_resize = self._on_page_resize
        except Exception: pass
        self.apply_theme()
        self.show_login()

    def apply_theme(self):
        self.page.theme_mode = ft.ThemeMode.DARK if STATE['dark'] else ft.ThemeMode.LIGHT
        self.page.bgcolor = T()['bg']
        if self.body is not None: self.body.bgcolor = T()['bg']

    def _clock_string(self):
        """رشته‌ی تاریخ و ساعت شمسی با ارقام فارسی."""
        now = datetime.now()
        try:
            jy, jm, jd = g2j(now.year, now.month, now.day)
        except Exception:
            jy, jm, jd = now.year, now.month, now.day
        trans = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")
        date_s = f"{jy}/{jm:02d}/{jd:02d}".translate(trans)
        time_s = f"{now.hour:02d}:{now.minute:02d}:{now.second:02d}".translate(trans)
        return f"{date_s}   •   {time_s}"

    def _tick_clock(self):
        """هر ثانیه متن ساعت را به‌روز می‌کند و خودش را دوباره زمان‌بندی می‌کند."""
        try:
            if self._clock_text is not None:
                self._clock_text.value = self._clock_string()
                self._clock_text.update()
        except Exception:
            pass
        if not self._clock_stop:
            try:
                self._clock_timer = threading.Timer(1.0, self._tick_clock)
                self._clock_timer.daemon = True
                self._clock_timer.start()
            except Exception:
                pass

    def _build_clock_widget(self):
        """ویجت ساعت زنده برای قرار دادن در AppBar."""
        self._clock_text = ft.Text(
            self._clock_string(),
            size=12,
            weight=ft.FontWeight.BOLD,
            color=T()['accent'],
            no_wrap=True,
        )
        return ft.Container(
            content=ft.Row([
                ft.Icon(_ic('SCHEDULE', 'ACCESS_TIME'), size=14, color=T()['accent']),
                self._clock_text,
            ], spacing=5, tight=True,
               vertical_alignment=ft.CrossAxisAlignment.CENTER),
            padding=pad_sym(10, 4),
            border_radius=10,
            bgcolor=alpha(T()['accent'], 0x1A),
            border=border_all(1, alpha(T()['accent'], 0x44)),
            margin=pad_only(right=8),
        )    
    def on_media_change(self, e=None):
        """هر بار ابعاد صفحه تغییر می‌کند (باز/بسته شدن کیبورد)، دوباره رندر می‌کنیم."""
        try:
            insets = self.page.media.view_insets
            self._kb_height = int(getattr(insets, "bottom", 0) or 0)
        except Exception:
            self._kb_height = 0
    def open_dlg(self, d):
        p = self.page
        for fn in ("show_dialog", "open"):
            f = getattr(p, fn, None)
            if callable(f):
                try: f(d); return
                except Exception: log_error(traceback.format_exc())
        try:
            p.dialog = d; d.open = True; p.update()
        except Exception: log_error(traceback.format_exc())

    def close_dlg(self, d=None):
        p = self.page
        for fn, args in (("pop_dialog", ()), ("close", (d,))):
            f = getattr(p, fn, None)
            if callable(f) and (fn != "close" or d is not None):
                try: f(*args); return
                except Exception: pass
        try:
            if d is not None: d.open = False
            p.update()
        except Exception: pass

    def toast(self, msg, error=False):
        if self._defer:
            self._queue.append((msg, error)); return
        sb = K(ft.SnackBar, content=ft.Text(msg, color="#ffffff", size=12),
               bgcolor="#c0392b" if error else T()['success'])
        self.open_dlg(sb)

    def confirm(self, msg, on_yes, title="تأیید", danger=True):
        def yes(e):
            self.close_dlg(d); on_yes()
        d = ft.AlertDialog(modal=True, title=ft.Text(title, size=14),
                           content=ft.Text(msg, size=12),
                           actions=[tbtn("انصراف", lambda e: self.close_dlg(d)),
                                    gbtn("بله", None, yes, "#c0392b" if danger else T()['primary'])])
        self.open_dlg(d)

    def info(self, title, msg):
        d = ft.AlertDialog(title=ft.Text(title, size=14),
                           content=ft.Container(
                               ft.Column([ft.Text(msg, selectable=True, size=12)],
                                         scroll=ft.ScrollMode.AUTO, tight=True),
                               width=min((self.page.width or 400) - 80, 380)),
                           actions=[tbtn("باشه", lambda e: self.close_dlg(d))])
        self.open_dlg(d)

    def file_dialog(self, path, title="✅ فایل ساخته شد", count=None):
        def do_open(ev):
            if not open_file(path):
                self.toast("باز کردن مستقیم ممکن نیست", True)

        def do_copy(ev):
            try:
                f = getattr(self.page, "set_clipboard", None)
                if callable(f): f(path)
                else: ft.Clipboard().set(path)
                self.toast("✅ مسیر کپی شد")
            except Exception:
                self.toast("کپی ممکن نشد", True)

        label = f"{title} ({count} فیش)" if count else title
        d = ft.AlertDialog(
            title=ft.Text(label, size=13),
            content=ft.Container(ft.Column([
                txt("مسیر فایل:", 12, color=T()['muted']),
                ft.Container(txt(path, 10, selectable=True),
                             bgcolor=T()['bg'], padding=8, border_radius=8),
            ], spacing=8, tight=True), width=min((self.page.width or 400) - 80, 360)),
            actions=[tbtn("📋 کپی مسیر", do_copy),
                     gbtn("📂 باز کردن", None, do_open, T()['success']),
                     tbtn("بستن", lambda e: self.close_dlg(d))])
        self.open_dlg(d)

    def show_login(self):
        p = self.page
        p.appbar = None; p.navigation_bar = None; p.floating_action_button = None
        pw = K(ft.TextField, label="رمز عبور", password=True, can_reveal_password=True,
               text_align=ft.TextAlign.CENTER, autofocus=True, width=240,
               **_border_kwargs(30))
        err = ft.Text("", color="#c0392b", size=11)

        def do(e):
            row = self.db.q1("SELECT admin_password FROM companies WHERE id=?", (self.cid,))
            stored = row['admin_password'] if row else ''
            now = time.monotonic()
            lock_until = getattr(self, '_login_lock_until', 0.0)
            if now < lock_until:
                remain = max(1, int(lock_until - now + 0.99))
                err.value = f"به دلیل تلاش ناموفق، {remain} ثانیه دیگر امتحان کنید."
                p.update()
                return
            if check_pw(pw.value or "", stored):
                self._login_failures = 0
                self._login_lock_until = 0.0
                if not (stored or '').startswith("pbkdf2$"):
                    self.db.x("UPDATE companies SET admin_password=? WHERE id=?",
                              (hash_pw(pw.value), self.cid))
                self.build_shell()
                if check_pw('1421', stored):
                    self.toast("رمز اولیه برنامه 1421 است؛ از بخش «بیشتر ← تغییر رمز» آن را عوض کنید.", True)
            else:
                failures = int(getattr(self, '_login_failures', 0)) + 1
                self._login_failures = failures
                if failures >= 5:
                    self._login_failures = 0
                    self._login_lock_until = time.monotonic() + 30.0
                    err.value = "۵ تلاش ناموفق؛ ورود برای ۳۰ ثانیه موقتاً متوقف شد."
                else:
                    err.value = f"رمز اشتباه است ({failures}/5)"
                pw.value = ""
                p.update()
        pw.on_submit = do
        box = ft.Container(
            width=300, padding=24, border_radius=24, bgcolor=T()['card'],
            border=border_all(2, T()['accent']),
            shadow=ft.BoxShadow(blur_radius=24, color="#22000000", offset=ft.Offset(0, 6)),
            content=ft.Column([
                ft.Container(ft.Icon(_ic("CALCULATE"), color=T()['primary'], size=36),
                             bgcolor=T()['accent'], width=68, height=68,
                             border_radius=34, alignment=center()),
                ft.Text("عرفان حساب", size=18, weight=ft.FontWeight.BOLD, color=T()['primary']),
                ft.Text("سیستم جامع حقوق و دستمزد", size=11, color=T()['muted']),
                pw,
                gbtn("ورود", _ic("LOGIN"), do, T()['primary'], width=240, height=44),
                err,
                ft.Text(f"{DEVELOPER} | {DEVELOPER_PHONE}", size=9, color=T()['muted']),
            ], horizontal_alignment=ft.CrossAxisAlignment.CENTER, spacing=10, tight=True))
        p.controls.clear()
        p.bgcolor = T()['primary']
        inner = ft.Container(box, alignment=center(), expand=True)
        safe = getattr(ft, "SafeArea", None)
        p.add(K(safe, content=inner, expand=True) if safe else inner)
        p.update()

    def build_shell(self):
        p = self.page
        self.apply_theme()
        self.body = ft.Container(expand=True, bgcolor=T()["bg"], padding=pad_sym(8, 6))
        # 🆕 ساعت زنده — قبل از ساخت AppBar بساز
        self._clock_stop = False
        clock_widget = self._build_clock_widget()

        self.appbar = K(ft.AppBar,
                        title=ft.Text(APP_TITLE, color=T()['accent'],
                                    weight=ft.FontWeight.BOLD, size=15),
                        center_title=True, bgcolor=T()['primary'], toolbar_height=52,
                        actions=[
                            clock_widget,
                            iconbtn(_ic("PALETTE"), self.theme_picker, T()['accent'], 20, "تغییر تم"),
                            iconbtn(_ic("DARK_MODE", "BRIGHTNESS_6"), self.toggle_theme,
                                    T()['accent'], 20, "شب/روز"),
                        ])

        # 🆕 شروع حلقه‌ی به‌روزرسانی ساعت
        if self._clock_timer is not None:
            try:
                self._clock_timer.cancel()
            except Exception:
                pass
        self._clock_timer = threading.Timer(1.0, self._tick_clock)
        self._clock_timer.daemon = True
        self._clock_timer.start()      
        self.navbar = K(ft.NavigationBar, selected_index=0,
                        on_change=lambda e: self.go_root(int(e.control.selected_index)),
                        bgcolor=T()['card'],
                        indicator_color=alpha(T()['accent'], 0x44), height=64,
                        destinations=[
                            ft.NavigationBarDestination(icon=_ic("DASHBOARD"), label="داشبورد"),
                            ft.NavigationBarDestination(icon=_ic("PEOPLE"), label="پرسنل"),
                            ft.NavigationBarDestination(icon=_ic("ACCESS_TIME"), label="کارکرد"),
                            ft.NavigationBarDestination(icon=_ic("PAYMENTS"), label="حقوق"),
                            ft.NavigationBarDestination(icon=_ic("MORE_HORIZ"), label="بیشتر")])
        p.controls.clear()
        p.appbar = self.appbar; p.navigation_bar = self.navbar

        # 🆕 بسته‌بندی body در SafeArea با محافظت از کیبورد
        safe = getattr(ft, "SafeArea", None)
        if safe:
            try:
                safe_body = K(safe, content=self.body, expand=True,
                            maintain_bottom_view_padding=True)
            except Exception:
                safe_body = self.body
        else:
            safe_body = self.body

        p.add(safe_body)
        self._on_page_resize()
        self.go_root(0)

    def roots(self):
        return [self.v_dashboard, self.v_employees, self.v_attendance, self.v_payroll, self.v_more]

    def go_root(self, i):
        if self.navbar: self.navbar.selected_index = i
        self.stack = [(self.TABS[i], self.roots()[i])]
        self.render()

    def push(self, title, builder):
        self.stack.append((title, builder)); self.render()

    def back(self, e=None):
        if len(self.stack) > 1:
            self.stack.pop(); self.render()

    def refresh(self, *_): self.render()

    def set_fab(self, icon, handler):
        try:
            self.page.floating_action_button = K(
                ft.FloatingActionButton, icon=icon, bgcolor=T()['accent'],
                foreground_color=T()['primary'], on_click=handler, mini=True)
        except Exception: pass

    def render(self):
        # Every page rebuild invalidates pending UI commands from the previous view.
        # This is particularly important for async scroll_to() responses in Flet Web.
        self._view_generation = int(getattr(self, "_view_generation", 0)) + 1
        title, builder = self.stack[-1]
        self._view_resize = None
        try: self.page.floating_action_button = None
        except Exception: pass
        try:
            content = builder()
        except Exception:
            tb = traceback.format_exc(); log_error(tb)
            content = ft.Column([txt("خطای نمایش", 14, True, "#c0392b"),
                                 ft.Text(tb, selectable=True, size=10)],
                                scroll=ft.ScrollMode.AUTO)
        self.body.content = content
        self.body.bgcolor = T()['bg']
        self.page.bgcolor = T()['bg']
        if self.appbar:
            self.appbar.title = ft.Text(title, color=T()['accent'],
                                        weight=ft.FontWeight.BOLD, size=15)
            self.appbar.bgcolor = T()['primary']
            self.appbar.leading = (iconbtn(_ic("ARROW_BACK"), self.back, T()['accent'], 20)
                                   if len(self.stack) > 1 else None)
        if self.navbar:
            self.navbar.bgcolor = T()['card']
            self.navbar.indicator_color = alpha(T()['accent'], 0x44)
        self.page.update()

    def theme_picker(self, e=None):
        def make_pick(theme_key):
            def handler(ev):
                STATE['theme'] = theme_key
                self.close_dlg(d); self.apply_theme()
                if self.stack: self.render()
            return handler
        items = []
        for k, th in THEMES.items():
            is_active = STATE['theme'] == k
            items.append(ft.Container(
                content=ft.Row([
                    ft.Container(width=26, height=26, bgcolor=th['primary'], border_radius=13),
                    ft.Container(width=26, height=26, bgcolor=th['accent'], border_radius=13),
                    txt(th['name'], 12, True, expand=True),
                    ft.Icon(_ic("CHECK"), color=T()['accent'], size=16) if is_active else ft.Container(),
                ], spacing=8),
                padding=10, border_radius=12, bgcolor=T()['card'], on_click=make_pick(k),
                border=border_all(2 if is_active else 1,
                                  T()['accent'] if is_active else T()['line'])))
        d = ft.AlertDialog(modal=True, title=ft.Text("🎨 انتخاب تم", size=14),
                           content=ft.Container(ft.Column(items, spacing=6, tight=True),
                                                width=min((self.page.width or 400) - 80, 340)),
                           actions=[tbtn("بستن", lambda e: self.close_dlg(d))])
        self.open_dlg(d)

    def toggle_theme(self, e=None):
        STATE['dark'] = not STATE['dark']
        self.apply_theme()
        if self.stack: self.render()

    def form(self, title, spec, init, on_save, on_delete=None):
        ctrls, rows = {}, []
        for f in spec:
            k, t = f['key'], f.get('type', 'text')
            v = init.get(k)
            if t == 'bool':
                c = K(ft.Switch, label=f['label'], value=bool(v), active_color=T()['accent'])
            elif t == 'dropdown':
                c = dd(f['label'], f['options'], None if v in (None, '') else v)
            elif t == 'password':
                c = K(ft.TextField, label=f['label'], password=True, can_reveal_password=True,
                      text_size=12, dense=True, **_border_kwargs(10))
            elif t == 'multiline':
                c = tf(f['label'], v, multiline=True, min_lines=3, max_lines=6)
            else:
                shown = ""
                if t not in ('int', 'float', 'money') and v not in (None, ''): shown = v
                elif t == 'money' and v not in (None, '', 0): shown = fmt(v)
                elif t in ('int', 'float') and v not in (None, '', 0): shown = v
                c = tf(f['label'], shown,
                       kb=t in ('int', 'float', 'money') or f.get('kb', False),
                       money=(t == 'money'), hint=f.get('hint'))
            ctrls[k] = c; rows.append((f, c))
        err = ft.Text("", color="#c0392b", size=11)

        def collect():
            out = {}
            for f in spec:
                c, t = ctrls[f['key']], f.get('type', 'text')
                if t == 'bool': out[f['key']] = 1 if c.value else 0
                elif t == 'dropdown':
                    val = c.value
                    cast = f.get('cast')
                    if cast and val not in (None, ''):
                        try: out[f['key']] = cast(val)
                        except (ValueError, TypeError): out[f['key']] = None
                    else: out[f['key']] = val
                elif t == 'password': out[f['key']] = c.value or ''
                else:
                    raw = (c.value or '').strip()
                    if t in ('money', 'int'):
                        if raw == '': out[f['key']] = None if f.get('blank_none') else 0
                        else: out[f['key']] = parse_int(raw)
                    elif t == 'float': out[f['key']] = parse_float(raw)
                    else: out[f['key']] = norm(raw) if f.get('kb') else raw
            return out

        def save(e):
            vals = collect()
            for f in spec:
                v = vals[f['key']]
                if f.get('required') and (v in ('', None) or
                                          (isinstance(v, (int, float)) and not isinstance(v, bool) and v == 0)):
                    err.value = f"«{f['label']}» الزامی است"; self.page.update(); return
            self._defer, self._queue = True, []
            try: msg = on_save(vals)
            except Exception as ex:
                log_error(traceback.format_exc()); msg = f"خطا: {ex}"
            self._defer = False
            if msg:
                self._queue = []; err.value = msg; self.page.update(); return
            self.close_dlg(d)
            queued, self._queue = self._queue, []
            self.render()
            for m, er in queued: self.toast(m, er)

        form_rows, pending = [], []
        full_keys = {'iban', 'address', 'first_name', 'last_name', 'notes'}
        for f, control in rows:
            if f.get('type') in ('bool', 'multiline') or f['key'] in full_keys:
                if pending:
                    form_rows.append(ft.Row(pending, spacing=6,
                                            vertical_alignment=ft.CrossAxisAlignment.START))
                    pending = []
                form_rows.append(control)
            else:
                try: control.expand = True
                except Exception: pass
                pending.append(control)
                if len(pending) == 2:
                    form_rows.append(ft.Row(pending, spacing=6,
                                            vertical_alignment=ft.CrossAxisAlignment.START))
                    pending = []
        if pending:
            form_rows.append(ft.Row(pending, spacing=6,
                                    vertical_alignment=ft.CrossAxisAlignment.START))
        w = min((self.page.width or 400) - 24, 600)
        h = min(max(((self.page.height or 700) - (self._kb_height or 0)) * 0.62, 260), 640)
        actions = [tbtn("انصراف", lambda e: self.close_dlg(d)),
                   gbtn("💾 ذخیره", None, save, T()['primary'])]
        if on_delete:
            actions.insert(0, tbtn("حذف", lambda e: self.confirm(
                "این مورد حذف شود؟", lambda: (self.close_dlg(d), on_delete())), "#c0392b"))
        d = ft.AlertDialog(modal=True, title=ft.Text(title, size=14),
                           content=ft.Container(ft.Column(form_rows + [err],
                                                          scroll=ft.ScrollMode.AUTO, spacing=8),
                                                width=w, height=h),
                           actions=actions)
        self.open_dlg(d)
   
    def open_jalali_date_picker(self, initial='', on_pick=None,
                                title='انتخاب تاریخ'):
        """انتخابگر تاریخ شمسی — طراحی ثابت برای همهٔ گوشی‌ها."""
        import time as _time

        # ─── قفل ضدِ باز/بسته شدن مکرر ───
        now = _time.time()
        last = getattr(self, '_date_picker_last', 0)
        if now - last < 0.6:
            return
        if getattr(self, '_date_picker_open', False):
            return
        self._date_picker_open = True
        self._date_picker_last = now

        # ─── تاریخ اولیه ───
        today = today_jalali()
        cy, cm, cd = today
        if initial:
            ok, _ = validate_jalali(initial)
            if ok:
                p = norm(initial).replace('-', '/').split('/')
                try:
                    cy, cm, cd = int(p[0]), int(p[1]), int(p[2])
                except (ValueError, IndexError):
                    pass

        state = {'y': cy, 'm': cm, 'd': cd}
        dlg_ref = {'dlg': None}

        # ─── ابعاد ثابت ───
        CELL = 40
        GAP = 3
        GRID_W = 7 * CELL + 6 * GAP       # 298
        CONTENT_W = GRID_W + 24           # 322

        # ─── انتخاب سال و ماه (کشویی) ───
        year_opts = [(str(y), str(y)) for y in range(1380, 1421)]
        month_opts = [(str(i), MONTHS[i - 1]) for i in range(1, 13)]

        def _dd_border(radius=8):
            try:
                if hasattr(ft, 'OutlineInputBorder'):
                    return ft.OutlineInputBorder(border_radius=radius)
            except Exception:
                pass
            return None

        _border = _dd_border(8)

        year_dd = ft.Dropdown(
            label='سال', value=str(cy),
            options=[ft.dropdown.Option(k, t) for k, t in year_opts],
            width=110, text_size=13,
            content_padding=pad_sym(8, 8), dense=True,
            enable_filter=True, enable_search=True, editable=True,
            **({'border': _border} if _border is not None else {}),
        )
        month_dd = ft.Dropdown(
            label='ماه', value=str(cm),
            options=[ft.dropdown.Option(k, t) for k, t in month_opts],
            expand=True, text_size=13,
            content_padding=pad_sym(8, 8), dense=True,
            **({'border': _border} if _border is not None else {}),
        )

        # ─── گرید روزها ───
        grid_holder = ft.Column(spacing=GAP, tight=True,
                                horizontal_alignment=ft.CrossAxisAlignment.CENTER)
        preview = ft.Text('', size=13, weight=ft.FontWeight.BOLD,
                          color=T()['primary'], text_align=ft.TextAlign.CENTER)
        start_info = ft.Text('', size=10, color=T()['muted'],
                             text_align=ft.TextAlign.CENTER)
        # ═══ بستن امن ═══
        def close_picker():
            self._date_picker_open = False
            self._date_picker_last = _time.time()
            d = dlg_ref.get('dlg')
            if d is not None:
                try:
                    self.close_dlg(d)
                except Exception:
                    pass

        def rebuild():
            # خواندن مقدار کشویی‌ها
            try:
                if year_dd.value: state['y'] = int(year_dd.value)
                if month_dd.value: state['m'] = int(month_dd.value)
            except (ValueError, TypeError):
                pass

            maxd = days_in_month(state['y'], state['m'])
            if state['d'] > maxd:
                state['d'] = maxd

            grid_holder.controls.clear()

            # ─── نام کوتاه و کامل روزها (شنبه=۰ ... جمعه=۶) ───
            DOW_SHORT = ['ش', 'ی', 'د', 'س', 'چ', 'پ', 'ج']
            DOW_FULL = ['شنبه', 'یک‌شنبه', 'دوشنبه', 'سه‌شنبه',
                        'چهارشنبه', 'پنج‌شنبه', 'جمعه']

            # رنگ هر ستون براساس روز هفته
            # ۰=شنبه ... ۵=پنج‌شنبه, ۶=جمعه
            def dow_color(i):
                if i == 6:      # جمعه
                    return T()['danger']
                if i == 5:      # پنج‌شنبه
                    return T()['info']
                return T()['muted']

            # ═══════ سرصفحه: نام حروف روزها (راست=شنبه، چپ=جمعه) ═══════
            header_cells = []
            for i, s in enumerate(DOW_SHORT):
                header_cells.append(ft.Container(
                    content=ft.Text(
                        s, size=12, weight=ft.FontWeight.BOLD,
                        color=dow_color(i),
                        text_align=ft.TextAlign.CENTER),
                    width=CELL, height=26, alignment=center(),
                    tooltip=DOW_FULL[i]))
            grid_holder.controls.append(ft.Container(
                content=ft.Row(header_cells, spacing=GAP,
                               vertical_alignment=ft.CrossAxisAlignment.CENTER),
                width=GRID_W,
                padding=pad_sym(0, 2)))

            # ═══════ روزهای ماه ═══════
            # jalali_weekday: ۰=شنبه ... ۶=جمعه
            # پس ستون j اُم نمایش = روز هفته j
            first_wd = jalali_weekday(state['y'], state['m'], 1)
            cells = [None] * first_wd + list(range(1, maxd + 1))
            while len(cells) % 7 != 0:
                cells.append(None)

            for row_idx in range(0, len(cells), 7):
                row_cells = []
                for col_idx in range(7):  # ۰=شنبه ... ۶=جمعه
                    d = cells[row_idx + col_idx]
                    if d is None:
                        row_cells.append(
                            ft.Container(width=CELL, height=CELL))
                        continue

                    is_sel = (d == state['d'])
                    is_today = (state['y'] == today[0]
                                and state['m'] == today[1]
                                and d == today[2])
                    is_friday = (col_idx == 6)

                    if is_sel:
                        bg = T()['primary']
                        fg = '#ffffff'
                        bd = T()['primary']
                        bw = 2
                    elif is_today:
                        bg = alpha(T()['accent'], 0x45)
                        fg = T()['primary']
                        bd = T()['accent']
                        bw = 2
                    elif is_friday:
                        bg = alpha(T()['danger'], 0x10)
                        fg = T()['danger']
                        bd = alpha(T()['danger'], 0x33)
                        bw = 1
                    else:
                        bg = T()['card']
                        fg = T()['text']
                        bd = alpha(T()['primary'], 0x22)
                        bw = 1

                    def mk_click(day):
                        def h(ev):
                            state['d'] = day
                            rebuild()
                        return h

                    row_cells.append(ft.Container(
                        content=ft.Text(
                            str(d), size=13,
                            weight=ft.FontWeight.BOLD,
                            color=fg,
                            text_align=ft.TextAlign.CENTER),
                        width=CELL, height=CELL,
                        bgcolor=bg, border_radius=8,
                        alignment=center(), ink=True,
                        border=border_all(bw, bd),
                        on_click=mk_click(d)))

                grid_holder.controls.append(ft.Container(
                    content=ft.Row(row_cells, spacing=GAP,
                                   vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    width=GRID_W))

            # ═══════ پیش‌نمایش با نام کامل روز ═══════
            try:
                wd_idx = jalali_weekday(state['y'], state['m'], state['d'])
                wd_name = DOW_FULL[wd_idx]
                today_mark = ''
                if (state['y'] == today[0] and state['m'] == today[1]
                        and state['d'] == today[2]):
                    today_mark = '  (امروز)'
                preview.value = (f"{wd_name}   {state['y']}/{state['m']:02d}/"
                                 f"{state['d']:02d}{today_mark}")
            except Exception:
                preview.value = (f"{state['y']}/{state['m']:02d}/"
                                 f"{state['d']:02d}")
            try:
                fw_idx = jalali_weekday(state['y'], state['m'], 1)
                fw_name = DOW_FULL[fw_idx]
                start_info.value = (f"شروع ماه: {fw_name} "
                                    f"(ستون «{DOW_SHORT[fw_idx]}» از راست)")
            except Exception:
                start_info.value = ''
            try:
                start_info.update()
            except Exception:
                pass
            try:
                grid_holder.update()
                preview.update()
            except Exception:
                pass

        def _sync_dd_values():
            """هم‌گام‌سازی مقدار کشویی‌ها با state."""
            try:
                yv = str(state['y'])
                mv = str(state['m'])
                if year_dd.value != yv:
                    year_dd.value = yv
                    try: year_dd.update()
                    except Exception: pass
                if month_dd.value != mv:
                    month_dd.value = mv
                    try: month_dd.update()
                    except Exception: pass
            except Exception:
                pass

        def on_year_change(e):
            # سال عوض شد → روز را در محدوده نگه دار و همه‌چیز را بازسازی کن
            try:
                if year_dd.value:
                    state['y'] = int(year_dd.value)
            except (ValueError, TypeError):
                pass
            maxd = days_in_month(state['y'], state['m'])
            if state['d'] > maxd:
                state['d'] = maxd
            _sync_dd_values()
            rebuild()

        def on_month_change(e):
            try:
                if month_dd.value:
                    state['m'] = int(month_dd.value)
            except (ValueError, TypeError):
                pass
            maxd = days_in_month(state['y'], state['m'])
            if state['d'] > maxd:
                state['d'] = maxd
            _sync_dd_values()
            rebuild()

        # اتصال مقاوم: هم on_change (Flet 0.28) هم on_select (Flet 1.0)
        def _bind_dd(dd_ctrl, handler):
            for attr in ('on_select', 'on_change'):
                try:
                    if hasattr(dd_ctrl, attr):
                        setattr(dd_ctrl, attr, handler)
                except Exception:
                    pass

        _bind_dd(year_dd, on_year_change)
        _bind_dd(month_dd, on_month_change)

        # ═══ دکمه‌ها ═══
        def do_confirm(e):
            v = f"{state['y']}/{state['m']:02d}/{state['d']:02d}"
            close_picker()
            if on_pick:
                try:
                    on_pick(v)
                except Exception:
                    log_error(traceback.format_exc())

        def do_clear(e):
            close_picker()
            if on_pick:
                try:
                    on_pick('')
                except Exception:
                    log_error(traceback.format_exc())

        def do_today(e):
            y, m, d = today
            state['y'], state['m'], state['d'] = y, m, d
            year_dd.value = str(y)
            month_dd.value = str(m)
            try:
                year_dd.update()
                month_dd.update()
            except Exception:
                pass
            rebuild()

        confirm_btn = _button("ElevatedButton", 'تأیید', _ic('CHECK'),
                              do_confirm, T()['success'], '#ffffff',
                              True, 46)
        today_btn = _button("OutlinedButton", 'امروز', _ic('TODAY'),
                            do_today, None, T()['primary'],
                            False, 46, 80)
        cancel_btn = _button("TextButton", 'انصراف', _ic('CLOSE'),
                             lambda e: close_picker(), None, T()['muted'],
                             False, 46, 80)

        # ═══ ساخت محتوای دیالوگ (عرض ثابت) ═══
        content = ft.Container(
            content=ft.Column([
                ft.Row([year_dd, month_dd], spacing=6,
                       vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Container(
                    content=ft.Text('شنبه تا جمعه — RTL',
                                    size=10, color=T()['muted'],
                                    text_align=ft.TextAlign.CENTER),
                    alignment=center()),
                ft.Divider(height=1, color=alpha(T()['primary'], 0x20)),
                grid_holder,
                # ⬇⬇⬇ این سه خط جدید را اضافه کن ⬇⬇⬇
                ft.Container(content=start_info, alignment=center()),
                # ⬆⬆⬆ پایان خطوط جدید ⬆⬆⬆
                ft.Container(height=2),
                ft.Container(
                    content=preview,
                    bgcolor=alpha(T()['primary'], 0x10),
                    padding=pad_sym(8, 6),
                    border_radius=8,
                    alignment=center(),
                    width=GRID_W,
                ),
                ft.Container(height=2),
                ft.Row([confirm_btn, today_btn, cancel_btn],
                       spacing=4),
            ], spacing=8, tight=True,
               horizontal_alignment=ft.CrossAxisAlignment.CENTER),
            width=CONTENT_W,
            padding=pad_sym(0, 4),
        )

        # ═══ دیالوگ ═══
        dlg = ft.AlertDialog(
            modal=True,
            title=ft.Row([
                ft.Icon(_ic('CALENDAR_MONTH'), size=18, color=T()['primary']),
                ft.Text(title, size=14, weight=ft.FontWeight.BOLD,
                        color=T()['primary'], expand=True),
                ft.IconButton(_ic('CLOSE'), icon_size=18,
                              icon_color=T()['muted'],
                              tooltip='بستن',
                              on_click=lambda e: close_picker()),
            ], spacing=6,
               vertical_alignment=ft.CrossAxisAlignment.CENTER),
            content=content,
            actions=[],
            content_padding=pad_sym(16, 8),
            title_padding=pad_sym(16, 12),
        )

        # اگر نسخه‌ای این را پشتیبانی کرد، حاشیهٔ امن اطراف دیالوگ را تنظیم می‌کند
        try:
            dlg.inset_padding = pad_sym(20, 40)
        except Exception:
            pass

        dlg_ref['dlg'] = dlg

        rebuild()
        self.open_dlg(dlg)
    def period_bar(self, on_change, with_month=True):
        def yc(e):
            y = parse_int(e.control.value)
            if 1300 <= y <= 1500 and y != self.year:
                self.year = y; on_change()
        def mc(e):
            self.month = int(e.control.value); on_change()
        row = [tf("سال", self.year, kb=True, width=90, on_change=yc, size=12)]
        if with_month:
            row.append(dd("ماه", [(i + 1, m) for i, m in enumerate(MONTHS)],
                        self.month, mc, expand=True))
        return ft.Row(row, spacing=6)
    def empty(self, msg, icon=None):
        return ft.Container(
            ft.Column([ft.Icon(icon or _ic("INBOX"), size=44, color=T()['muted']),
                       txt(msg, 12, color=T()['muted'], align=ft.TextAlign.CENTER)],
                      horizontal_alignment=ft.CrossAxisAlignment.CENTER, spacing=6),
            padding=30, alignment=center())

    # ── داشبورد ──
    def v_dashboard(self):
        c = self.db.company_data(self.cid)
        active = [e for e in c['employees'] if e['is_active']]
        pays = self.svc.payrolls(self.cid, self.year, self.month)
        gross = sum(p['gross_salary'] for p in pays)
        net = sum(p['net_salary'] for p in pays)
        jy, jm, jd = today_jalali()
        hdr = ft.Container(
            padding=16, border_radius=16,
            gradient=ft.LinearGradient(begin=ft.Alignment(-1, 0), end=ft.Alignment(1, 0),
                           colors=[T()['primary'], T()['primary_dark']]),
            content=ft.Column([
                txt(c.get('name') or APP_TITLE, 17, True, T()['accent']),
                txt(f"امروز: {jy}/{jm:02d}/{jd:02d} • دوره: {MONTHS[self.month - 1]} {self.year}",
                    11, color="#ccffffff")], spacing=4))

        def stat(icon, color, val, label):
            return ft.Container(
                content=ft.Column([
                    ft.Container(ft.Icon(icon, color=color, size=20),
                                 bgcolor=alpha(color, 0x22), width=38, height=38,
                                 border_radius=19, alignment=center()),
                    txt(val, 13, True), txt(label, 10, color=T()['muted']),
                ], spacing=2, horizontal_alignment=ft.CrossAxisAlignment.CENTER),
                padding=10, bgcolor=T()['card'], border_radius=12,
                border=border_all(1, T()['line']))
        grid = ft.Column([
            ft.Row([ft.Container(stat(_ic("PEOPLE"), T()['accent'], len(active), "پرسنل فعال"), expand=True),
                    ft.Container(stat(_ic("RECEIPT_LONG"), T()['success'], len(pays),
                                      f"فیش {MONTHS[self.month - 1]}"), expand=True)]),
            ft.Row([ft.Container(stat(_ic("TRENDING_UP"), T()['info'], fmt(gross), "جمع ناخالص"), expand=True),
                    ft.Container(stat(_ic("ACCOUNT_BALANCE_WALLET"), T()['danger'], fmt(net), "جمع خالص"), expand=True)]),
        ], spacing=6)
        quick = card(ft.Column([
            txt("⚡ اقدامات سریع", 13, True),
            wide(lambda: gbtn("تایم‌شیت", _ic("ACCESS_TIME"), lambda e: self.go_root(2), T()['primary'], expand=True)),
            wide(lambda: gbtn("محاسبه حقوق", _ic("CALCULATE"), lambda e: self.go_root(3), T()['success'], expand=True)),
            wide(lambda: obtn("گزارشات", _ic("ASSESSMENT"),
                              lambda e: self.push("گزارشات", self.v_reports), expand=True)),
        ], spacing=6))
        items = [hdr, grid, quick]
        if not c['employees']:
            items.insert(1, card(ft.Column([
                txt("هنوز پرسنلی ثبت نشده", 13, True),
                txt("از بخش «پرسنل» شروع کنید یا داده نمونه را بارگذاری کنید.", 11, color=T()['muted']),
                obtn("بارگذاری داده نمونه", _ic("SCIENCE"), self.load_sample)]),
                border_color=T()['accent']))
        return ft.ListView(items, spacing=8, expand=True, padding=pad_only(bottom=16))

    def load_sample(self, e=None):
        ok = self.db.seed_sample(self.cid)
        if ok: self.year, self.month = STD['year'], 1
        self.toast("داده نمونه اضافه شد" if ok else "پرسنلی موجود است", not ok)
        self.refresh()

    # ── پرسنل ──
    def emp_spec(self, depts):
        return [
            dict(key='personnel_code', label='کد پرسنلی', kb=True),
            dict(key='first_name', label='نام', required=True),
            dict(key='last_name', label='نام خانوادگی', required=True),
            dict(key='national_code', label='کد ملی (اختیاری)', kb=True),
            dict(key='father_name', label='نام پدر'),
            dict(key='id_number', label='شماره شناسنامه', kb=True),
            dict(key='id_issue_place', label='محل صدور'),
            dict(key='birth_date', label='تاریخ تولد', hint='1365/05/10'),
            dict(key='birth_place', label='محل تولد'),
            dict(key='employment_date', label='تاریخ استخدام', hint='1404/01/01'),
            dict(key='contract_type', label='نوع قرارداد', type='dropdown',
                 options=[('رسمی','رسمی'), ('آزمایشی','آزمایشی'), ('پیمانکاری','پیمانکاری'),
                          ('موقت','موقت'), ('ساعتی','ساعتی')]),
            dict(key='contract_end', label='پایان قرارداد', hint='1405/12/29'),
            dict(key='dept_id', label='دپارتمان', type='dropdown',
                 options=[(d['id'], d['title']) for d in depts], cast=int),
            dict(key='job_title', label='عنوان شغلی'),
            dict(key='education', label='مدرک تحصیلی', type='dropdown',
                 options=[('','—'), ('زیر دیپلم','زیر دیپلم'), ('دیپلم','دیپلم'),
                          ('کاردانی','کاردانی'), ('کارشناسی','کارشناسی'),
                          ('کارشناسی ارشد','کارشناسی ارشد'), ('دکترا','دکترا')]),
            dict(key='insurance_number', label='شماره بیمه', kb=True),
            dict(key='insurance_exempt', label='عدم شمول بیمه (صرفاً با مجوز قانونی)', type='bool'),
            dict(key='tax_exempt', label='عدم شمول مالیات (صرفاً با مجوز قانونی)', type='bool'),
            dict(key='shift_pattern', label='الگوی نوبت‌کاری', type='dropdown',
                 options=[('none','غیرنوبت‌کار'), ('morning_evening','صبح و عصر، ۱۰٪'),
                          ('morning_evening_night','صبح/عصر/شب، ۱۵٪'),
                          ('morning_night','صبح و شب، ۲۲٫۵٪'), ('evening_night','عصر و شب، ۲۲٫۵٪')]),
            dict(key='daily_salary', label='حقوق روزانه (ریال)', type='money', required=True),
            dict(key='base_hours', label='ساعت ماهانه', type='dropdown', cast=int,
                 options=[(0, 'پیش‌فرض (220)'), (176, '176'), (192, '192'),
                          (205, '205'), (220, '220'), (240, '240')]),
            dict(key='marital', label='متاهل', type='bool'),
            dict(key='child_count', label='تعداد فرزند', type='int'),
            dict(key='mobile', label='تلفن همراه', kb=True),
            dict(key='phone', label='تلفن ثابت', kb=True),
            dict(key='address', label='آدرس محل سکونت', type='multiline'),
            dict(key='postal_code', label='کد پستی', kb=True),
            dict(key='emergency_name', label='نام تماس اضطراری'),
            dict(key='emergency_phone', label='تلفن اضطراری', kb=True),
            dict(key='card_number', label='شماره کارت', kb=True),
            dict(key='account_number', label='شماره حساب', kb=True),
            dict(key='iban', label='شبا (IR...)'),
            dict(key='bank_name', label='نام بانک'),
            dict(key='tax_file_code', label='کد پرونده مالیاتی', kb=True),
            dict(key='notes', label='یادداشت', type='multiline'),
            dict(key='is_active', label='فعال', type='bool'),
        ]

    def emp_form(self, emp):
        """فرم تمام‌صفحه پرسنل با بخش‌های بازشو (آکاردئون) و انتخابگر تاریخ شمسی."""
        depts = self.db.q("SELECT * FROM departments WHERE company_id=?", (self.cid,))

        # ═══════════ مقدار اولیه ═══════════
        if emp:
            init = dict(emp)
        else:
            init = dict(
                is_active=1, marital=0, child_count=0,
                employment_date=jalali_today_str(), contract_type='رسمی',
                dept_id=depts[0]['id'] if depts else None,
                insurance_exempt=0, tax_exempt=0, shift_pattern='none',
                base_hours=0,
            )
            yr = self.db.q1(
                'SELECT * FROM rate_years WHERE company_id=? AND year<=? '
                'ORDER BY year DESC LIMIT 1', (self.cid, self.year))
            init['daily_salary'] = ((yr or {}).get('min_daily_wage')
                                    or STD['min_daily_wage'])
        init['base_hours'] = (emp or {}).get('base_hours') or 0

        ctrls = {}

        # ─────── سازندهٔ کنترل‌ها ───────
        def _set_ctrl_value(ctrl, val):
            ctrl.value = val
            try: ctrl.update()
            except Exception: pass

        def add_text(key, label, **kw):
            c = tf(label, init.get(key), expand=True, **kw)
            ctrls[key] = c

        def add_money(key, label):
            v = init.get(key)
            shown = fmt(v) if v not in (None, '', 0) else ''
            ctrls[key] = tf(label, shown, kb=True, money=True, expand=True)

        def add_int(key, label):
            v = init.get(key)
            ctrls[key] = tf(label, v if v not in (None, '') else '',
                            kb=True, expand=True)

        def add_dd(key, label, options):
            ctrls[key] = dd(label, options, init.get(key), expand=True)

        def add_switch(key, label):
            ctrls[key] = K(ft.Switch, label=label,
                        value=bool(init.get(key)),
                        active_color=T()['accent'])

        def add_multiline(key, label):
            c = tf(label, init.get(key), multiline=True, expand=True)
            try:
                c.min_lines = 2; c.max_lines = 4
            except Exception: pass
            ctrls[key] = c

        def add_date(key, label):
            field = tf(label, init.get(key), expand=True, read_only=True,
                       prefix=_ic('CALENDAR_MONTH'))
            try:
                field.read_only = True
            except Exception:
                pass

            def open_picker(e=None):
                if getattr(self, '_date_picker_open', False):
                    return
                def _on_pick(v):
                    field.value = v or ''
                    try:
                        field.update()
                    except Exception:
                        pass
                self.open_jalali_date_picker(
                    field.value or '',
                    on_pick=_on_pick,
                    title=label)

            try:
                field.on_click = open_picker
            except Exception:
                pass

            # ⚠️ هیچ on_focus‌ای اینجا نگذار

            ctrls[key] = field

        # ─────── تعریف فیلدها ───────
        add_text('first_name', 'نام *')
        add_text('last_name', 'نام خانوادگی *')
        add_text('father_name', 'نام پدر')
        add_text('national_code', 'کد ملی', kb=True)
        add_text('id_number', 'شماره شناسنامه', kb=True)
        add_text('id_issue_place', 'محل صدور')
        add_date('birth_date', 'تاریخ تولد')
        add_text('birth_place', 'محل تولد')

        add_text('personnel_code', 'کد پرسنلی', kb=True)
        add_date('employment_date', 'تاریخ استخدام')
        add_dd('contract_type', 'نوع قرارداد',
            [('رسمی', 'رسمی'), ('آزمایشی', 'آزمایشی'),
                ('پیمانکاری', 'پیمانکاری'), ('موقت', 'موقت'),
                ('ساعتی', 'ساعتی')])
        add_date('contract_end', 'پایان قرارداد')
        add_dd('dept_id', 'دپارتمان',
            [(d['id'], d['title']) for d in depts])
        add_text('job_title', 'عنوان شغلی')
        add_dd('education', 'مدرک تحصیلی',
            [('', '—'), ('زیر دیپلم', 'زیر دیپلم'), ('دیپلم', 'دیپلم'),
                ('کاردانی', 'کاردانی'), ('کارشناسی', 'کارشناسی'),
                ('کارشناسی ارشد', 'کارشناسی ارشد'), ('دکترا', 'دکترا')])
        add_dd('shift_pattern', 'الگوی نوبت‌کاری',
            [('none', 'غیرنوبت‌کار'),
                ('morning_evening', 'صبح و عصر، ۱۰٪'),
                ('morning_evening_night', 'صبح/عصر/شب، ۱۵٪'),
                ('morning_night', 'صبح و شب، ۲۲٫۵٪'),
                ('evening_night', 'عصر و شب، ۲۲٫۵٪')])

        add_money('daily_salary', 'حقوق روزانه (ریال) *')
        add_dd('base_hours', 'ساعت ماهانه',
            [(0, 'پیش‌فرض (220)'), (176, '176'), (192, '192'),
                (205, '205'), (220, '220'), (240, '240')])
        add_text('insurance_number', 'شماره بیمه', kb=True)
        add_text('tax_file_code', 'کد پرونده مالیاتی', kb=True)
        add_switch('insurance_exempt', 'عدم شمول بیمه (با مجوز قانونی)')
        add_switch('tax_exempt', 'عدم شمول مالیات (با مجوز قانونی)')

        add_switch('marital', 'متاهل')
        add_int('child_count', 'تعداد فرزند')

        add_text('mobile', 'تلفن همراه', kb=True)
        add_text('phone', 'تلفن ثابت', kb=True)
        add_text('postal_code', 'کد پستی', kb=True)
        add_text('emergency_name', 'نام تماس اضطراری')
        add_text('emergency_phone', 'تلفن اضطراری', kb=True)
        add_multiline('address', 'آدرس محل سکونت')

        add_text('card_number', 'شماره کارت', kb=True)
        add_text('account_number', 'شماره حساب', kb=True)
        add_text('iban', 'شبا (IR...)')
        add_text('bank_name', 'نام بانک')

        add_multiline('notes', 'یادداشت')
        add_switch('is_active', 'فعال')

        # ═══════════ جمع‌آوری مقادیر ═══════════
        TEXT_KEYS = ['personnel_code', 'first_name', 'last_name', 'national_code',
                    'father_name', 'id_number', 'id_issue_place', 'birth_date',
                    'birth_place', 'employment_date', 'contract_end', 'job_title',
                    'insurance_number', 'mobile', 'phone', 'address', 'postal_code',
                    'emergency_name', 'emergency_phone', 'card_number',
                    'account_number', 'iban', 'bank_name', 'tax_file_code', 'notes']
        INT_KEYS = ['daily_salary', 'child_count']
        BOOL_KEYS = ['marital', 'is_active', 'insurance_exempt', 'tax_exempt']
        DD_KEYS = ['contract_type', 'education', 'shift_pattern']
        DATE_KEYS = ['employment_date', 'birth_date', 'contract_end']

        def collect():
            out = {}
            for k in TEXT_KEYS:
                if k in ctrls:
                    out[k] = (ctrls[k].value or '').strip()
            for k in INT_KEYS:
                if k in ctrls:
                    out[k] = parse_int(ctrls[k].value)
            for k in BOOL_KEYS:
                if k in ctrls:
                    out[k] = 1 if ctrls[k].value else 0
            for k in DD_KEYS:
                if k in ctrls:
                    out[k] = ctrls[k].value or ''
            if 'dept_id' in ctrls:
                v = ctrls['dept_id'].value
                try:
                    out['dept_id'] = int(v) if v not in (None, '') else None
                except (ValueError, TypeError):
                    out['dept_id'] = None
            if 'base_hours' in ctrls:
                v = ctrls['base_hours'].value
                try:
                    n = int(v) if v not in (None, '') else 0
                    out['base_hours'] = n if n > 0 else None
                except (ValueError, TypeError):
                    out['base_hours'] = None
            return out

        # ═══════════ ذخیره ═══════════
        def do_save(e=None):
            v = collect()
            if not v.get('first_name'):
                self.toast('نام الزامی است', True); return
            if not v.get('last_name'):
                self.toast('نام خانوادگی الزامی است', True); return
            if (v.get('daily_salary') or 0) <= 0:
                self.toast('حقوق روزانه معتبر نیست', True); return
            nc = norm(v.get('national_code') or '')
            if nc and not (nc.isdigit() and len(nc) == 10):
                self.toast('کد ملی باید ۱۰ رقم عددی باشد', True); return
            v['national_code'] = nc or None
            for k in DATE_KEYS:
                d = norm(v.get(k) or '')
                if d:
                    ok, msg = validate_jalali(d)
                    if not ok:
                        self.toast(f'تاریخ نامعتبر: {msg}', True); return
                    v[k] = d.replace('-', '/')
            if not v.get('personnel_code'):
                existing = self.db.q(
                    'SELECT personnel_code FROM employees WHERE company_id=?',
                    (self.cid,))
                nums = [parse_int(x.get('personnel_code')) for x in existing
                        if norm(x.get('personnel_code') or '').isdigit()]
                v['personnel_code'] = f"{max(nums or [1000]) + 1:04d}"
            v['iban'] = (v.get('iban') or '').upper().replace(' ', '')
            if not v.get('created_at'):
                v['created_at'] = jalali_today_str()
            try:
                if emp:
                    self.db.update('employees', emp['id'], v)
                else:
                    self.db.insert('employees', dict(v, company_id=self.cid))
            except sqlite3.IntegrityError:
                self.toast('این کد ملی قبلاً ثبت شده است', True); return
            self.toast('✅ پرسنل ذخیره شد')
            self.back()
            self.refresh()

        def do_delete(e=None):
            def go():
                self.db.delete('employees', emp['id'])
                self.toast('🗑 پرسنل حذف شد')
                self.back(); self.refresh()
            self.confirm(
                'با حذف پرسنل، تمام سوابق مرتبط حذف می‌شوند. ادامه می‌دهید؟',
                go, 'حذف پرسنل')

        # ═══════════ سازندهٔ بخش آکاردئونی ═══════════
        def field_cell(key):
            c = ctrls.get(key)
            if c is None:
                return ft.Container(expand=True)
            try: c.expand = True
            except Exception: pass
            return ft.Container(content=c, expand=True)

        def make_section(title, color, rows, initially_open=True):
            body = ft.Column(spacing=8, tight=True)
            for row_keys in rows:
                if len(row_keys) == 1:
                    body.controls.append(
                        ft.Container(content=field_cell(row_keys[0]),
                                    padding=pad_sym(0, 2)))
                else:
                    body.controls.append(ft.Row(
                        [field_cell(k) for k in row_keys], spacing=8,
                        vertical_alignment=ft.CrossAxisAlignment.START))
            body.visible = initially_open

            arrow = ft.Icon(
                _ic('EXPAND_LESS') if initially_open else _ic('EXPAND_MORE'),
                color=color, size=20)

            def toggle(e):
                body.visible = not body.visible
                new_icon = _ic('EXPAND_LESS') if body.visible else _ic('EXPAND_MORE')
                try:
                    arrow.name = new_icon
                except Exception:
                    try: arrow.icon = new_icon
                    except Exception: pass
                try:
                    body.update(); arrow.update()
                except Exception:
                    pass

            header = ft.Container(
                content=ft.Row([
                    ft.Container(width=4, height=22, bgcolor=color,
                                border_radius=2),
                    txt(title, 13, True, color, expand=True),
                    arrow,
                ], spacing=10,
                vertical_alignment=ft.CrossAxisAlignment.CENTER),
                padding=pad_sym(8, 6),
                on_click=toggle, ink=True, border_radius=10)

            return ft.Container(
                content=ft.Column([header, body], spacing=6, tight=True),
                padding=8,
                bgcolor=alpha(color, 0x10),
                border=border_all(1, alpha(color, 0x33)),
                border_radius=14)

        # ═══════════ بخش‌ها ═══════════
        sections = [
            make_section('🪪 اطلاعات هویتی', T()['primary'], [
                ('first_name', 'last_name'),
                ('father_name', 'national_code'),
                ('id_number', 'id_issue_place'),
                ('birth_date', 'birth_place'),
            ], initially_open=True),

            make_section('💼 اطلاعات شغلی', T()['accent'], [
                ('personnel_code', 'employment_date'),
                ('contract_type', 'contract_end'),
                ('dept_id', 'job_title'),
                ('education', 'shift_pattern'),
            ], initially_open=True),

            make_section('💰 اطلاعات مالی و بیمه', T()['success'], [
                ('daily_salary', 'base_hours'),
                ('insurance_number', 'tax_file_code'),
                ('insurance_exempt',),
                ('tax_exempt',),
            ], initially_open=True),

            make_section('👨‍👩‍👧 وضعیت خانوادگی', T()['purple'], [
                ('marital', 'child_count'),
            ], initially_open=True),

            make_section('📞 اطلاعات تماس', T()['info'], [
                ('mobile', 'phone'),
                ('postal_code', 'emergency_name'),
                ('emergency_phone',),
                ('address',),
            ], initially_open=False),

            make_section('🏦 اطلاعات بانکی', T()['warning'], [
                ('card_number', 'account_number'),
                ('iban', 'bank_name'),
            ], initially_open=False),

            make_section('📝 یادداشت و وضعیت', T()['muted'], [
                ('notes',),
                ('is_active',),
            ], initially_open=False),
        ]

        # ═══════════ اجزای جانبی ═══════════
        def build_top_bar():
            btns = [
                gbtn('💾 ذخیره', _ic('SAVE'), do_save, T()['success'], height=42),
                obtn('انصراف', _ic('ARROW_BACK'),
                    lambda e: self.back(), height=42),
            ]
            if emp:
                btns.append(tbtn('🗑 حذف', do_delete, '#c0392b'))
            return ft.Container(
                content=ft.Row(btns, spacing=8,
                            vertical_alignment=ft.CrossAxisAlignment.CENTER),
                padding=pad_sym(4, 8))

        def build_header():
            if not emp:
                return ft.Container()
            name = f"{emp.get('first_name','')} {emp.get('last_name','')}".strip()
            initials = ((emp.get('first_name') or '?')[:1] +
                        (emp.get('last_name') or '')[:1])
            return ft.Container(
                content=ft.Row([
                    ft.Container(
                        content=txt(initials, 16, True, '#ffffff'),
                        width=48, height=48, bgcolor=T()['primary'],
                        border_radius=24, alignment=center()),
                    ft.Column([
                        txt(name or 'بدون نام', 14, True),
                        txt(f"کد پرسنلی: {emp.get('personnel_code') or emp.get('id')} • "
                            f"کد ملی: {emp.get('national_code') or '-'}",
                            10, color=T()['muted']),
                    ], spacing=2, expand=True),
                ], spacing=12,
                vertical_alignment=ft.CrossAxisAlignment.CENTER),
                padding=12, bgcolor=T()['card'], border_radius=14,
                border=border_all(1, T()['line']))

        hint_bar = ft.Container(
            content=ft.Row([
                ft.Icon(_ic('INFO_OUTLINE'), size=16, color=T()['primary']),
                txt('فیلدهای ستاره‌دار الزامی‌اند. تاریخ‌ها را با کلیک روی '
                    'فیلد از تقویم شمسی انتخاب کنید.',
                    10, color=T()['muted'], expand=True),
            ], spacing=6, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            padding=pad_sym(10, 6),
            bgcolor=alpha(T()['primary'], 0x10), border_radius=10)

        def build():
            self.set_fab(_ic('SAVE'), do_save)
            content = ft.Column([
                build_header(),
                hint_bar,
                *sections,
                ft.Container(height=100),
            ], spacing=10, tight=True)
            return ft.Column([
                build_top_bar(),
                ft.ListView([content], expand=True, spacing=0, padding=pad_sym(8, 4)),
            ], expand=True, spacing=0)

        title = (f"✏️ ویرایش پرسنل — {emp.get('first_name','')} "
                f"{emp.get('last_name','')}".strip()
                if emp else "➕ پرسنل جدید")
        self.push(title, build)
    def emp_detail(self, emp):
        depts = {d['id']: d for d in self.db.q("SELECT * FROM departments WHERE company_id=?", (self.cid,))}
        dept = depts.get(emp.get('dept_id'))
        photo_widget = None
        photo_b64 = emp.get('photo') or ''
        if photo_b64:
            try:
                photo_widget = ft.Container(_img_ctl(photo_b64, 90, 90, 45),
                                            width=100, height=100, alignment=center())
            except Exception: photo_widget = None
        if not photo_widget:
            initials = (emp.get('first_name') or '?')[:1] + (emp.get('last_name') or '')[:1]
            photo_widget = ft.Container(
                ft.Text(initials, size=28, weight=ft.FontWeight.BOLD, color=T()['primary']),
                width=100, height=100, bgcolor=T()['accent'], border_radius=50, alignment=center())

        async def up_photo(e): await self._pick_photo(emp['id'])

        def info_row(label, val):
            if not val: return None
            return ft.Row([txt(label, 11, color=T()['muted'], width=110),
                           txt(str(val), 11, True, expand=True)], spacing=4)

        info_items = [
            info_row('نام و فامیل', f"{emp.get('first_name','')} {emp.get('last_name','')}"),
            info_row('کد پرسنلی', emp.get('personnel_code')),
            info_row('کد ملی', emp.get('national_code')),
            info_row('نام پدر', emp.get('father_name')),
            info_row('شماره شناسنامه', emp.get('id_number')),
            info_row('محل صدور', emp.get('id_issue_place')),
            info_row('تاریخ تولد', emp.get('birth_date')),
            info_row('محل تولد', emp.get('birth_place')),
            info_row('تاریخ استخدام', emp.get('employment_date')),
            info_row('نوع قرارداد', emp.get('contract_type')),
            info_row('پایان قرارداد', emp.get('contract_end')),
            info_row('دپارتمان', dept.get('title') if dept else None),
            info_row('عنوان شغلی', emp.get('job_title')),
            info_row('مدرک تحصیلی', emp.get('education')),
            info_row('شماره بیمه', emp.get('insurance_number')),
            info_row('حقوق روزانه', fmt(emp.get('daily_salary') or 0) + ' ریال'),
            info_row('حقوق ماهانه', fmt((emp.get('daily_salary') or 0) * 30) + ' ریال'),
            info_row('وضعیت تاهل', 'متاهل' if emp.get('marital') else 'مجرد'),
            info_row('تعداد فرزند', emp.get('child_count')),
            info_row('تلفن همراه', emp.get('mobile')),
            info_row('تلفن ثابت', emp.get('phone')),
            info_row('آدرس', emp.get('address')),
            info_row('کد پستی', emp.get('postal_code')),
            info_row('تماس اضطراری', f"{emp.get('emergency_name','')} - {emp.get('emergency_phone','')}"),
            info_row('شماره کارت', emp.get('card_number')),
            info_row('شماره حساب', emp.get('account_number')),
            info_row('شبا', emp.get('iban')),
            info_row('نام بانک', emp.get('bank_name')),
            info_row('کد پرونده مالیاتی', emp.get('tax_file_code')),
            info_row('یادداشت', emp.get('notes')),
        ]
        info_items = [x for x in info_items if x is not None]

        def open_edit(e):
            self.close_dlg(dlg); self.emp_form(emp)

        def open_contract(e):
            self.close_dlg(dlg); self.debounce('open_contract', lambda: self.contract_view(emp), 0.3)

        dlg = ft.AlertDialog(
            title=ft.Text(f"👤 {emp.get('first_name','')} {emp.get('last_name','')}", size=14),
            content=ft.Container(
                ft.Column([
                    ft.Row([photo_widget,
                            ft.Column([
                                txt(f"#{emp.get('personnel_code') or emp['id']}", 12, True),
                                badge('فعال' if emp.get('is_active') else 'غیرفعال',
                                      '#dcfce7' if emp.get('is_active') else '#fee2e2',
                                      '#166534' if emp.get('is_active') else '#991b1b', 9),
                                obtn("📷 تغییر عکس", _ic("PHOTO_CAMERA"), up_photo, height=32),
                            ], spacing=6, alignment=ft.MainAxisAlignment.CENTER)],
                           spacing=12),
                    ft.Divider(height=1),
                    *info_items,
                    ft.Divider(height=1),
                    ft.Row([
                        gbtn("✏️ ویرایش", _ic("EDIT"), open_edit, T()['primary'], expand=True),
                        gbtn("📄 قرارداد", _ic("DESCRIPTION"), open_contract, T()['success'], expand=True),
                    ], spacing=6),
                ], scroll=ft.ScrollMode.AUTO, spacing=6, tight=True),
                width=min((self.page.width or 400) - 60, 420),
                height=min((self.page.height or 700) * 0.7, 560)),
            actions=[tbtn("بستن", lambda e: self.close_dlg(dlg))])
        self.open_dlg(dlg)
        self._emp_dlg = dlg

    def _pick_photo(self, emp_id):
        try:
            fp = K(ft.FilePicker, on_result=lambda e: self._on_photo_picked(e, emp_id))
            self.page.overlay.append(fp)
            self.page.update()
            try: fp.pick_files(allow_multiple=False, allowed_extensions=["jpg","jpeg","png","webp"], with_data=True)
            except Exception:
                try: fp.pick_files()
                except Exception: pass
        except Exception:
            log_error(traceback.format_exc())
            self.toast("انتخاب فایل در این نسخه پشتیبانی نمی‌شود", True)

    def _on_photo_picked(self, e, emp_id):
        try:
            files = getattr(e, 'files', None) or []
            if not files:
                p = getattr(e, 'path', None)
                if p: files = [type('F', (), {'path': p})()]
            if not files: return
            f = files[0]
            path = getattr(f, 'path', None)
            if not path or not os.path.isfile(path): return
            with open(path, 'rb') as fh: data = fh.read()
            if Image is not None:
                try:
                    img = Image.open(io.BytesIO(data))
                    img.thumbnail((400, 400))
                    buf = io.BytesIO()
                    img.convert('RGB').save(buf, format='JPEG', quality=80)
                    data = buf.getvalue()
                except Exception: pass
            b64 = base64.b64encode(data).decode('ascii')
            self.db.update('employees', emp_id, {'photo': b64})
            self.toast("✅ عکس ذخیره شد"); self.refresh()
        except Exception:
            log_error(traceback.format_exc())
            self.toast("خطا در ذخیره عکس", True)

    def v_employees(self):
        c = {'employees': self.db.q("SELECT * FROM employees WHERE company_id=? ORDER BY id", (self.cid,)),
             'departments': self.db.q("SELECT * FROM departments WHERE company_id=?", (self.cid,))}
        depts = {d['id']: d for d in c['departments']}
        state = {'q': '', 'dept': '', 'status': 'active', 'sort': 'name'}
        holder = ft.ListView(spacing=4, expand=True)
        count_holder = ft.Container()

        def row_for(emp, idx=0):
            avatar = None
            if emp.get('photo'):
                try:
                    avatar = ft.Container(_img_ctl(emp['photo'], 48, 48, 24), width=48, height=48)
                except Exception: avatar = None
            if not avatar:
                ini = (emp.get('first_name') or '?')[:1] + (emp.get('last_name') or '')[:1]
                avatar = ft.Container(
                    ft.Text(ini, size=15, weight=ft.FontWeight.BOLD, color=T()['primary']),
                    width=48, height=48, bgcolor=T()['accent'], border_radius=24, alignment=center())

            dept_name = (depts.get(emp.get('dept_id')) or {}).get('title', '-')
            return ft.Container(
                content=ft.Row([
                    txt(str(idx), 7, color=T()['muted'], width=14, align=ft.TextAlign.CENTER),
                    avatar,
                    ft.Column([
                        ft.Row([
                            txt(f"{emp.get('first_name','')} {emp.get('last_name','')}",
                                13, True, no_wrap=True, overflow=ft.TextOverflow.ELLIPSIS, expand=True),
                            badge('●' if emp.get('is_active') else '○',
                                  '#dcfce7' if emp.get('is_active') else '#fee2e2',
                                  '#166534' if emp.get('is_active') else '#991b1b', 8),
                        ], spacing=4),
                        txt(f"{emp.get('job_title') or 'بدون شغل'} • {dept_name} • "
                            f"کد ملی: {emp.get('national_code','')}",
                            10, color=T()['muted'], no_wrap=True, overflow=ft.TextOverflow.ELLIPSIS),
                        txt(f"استخدام: {emp.get('employment_date') or '-'} • "
                            f"حقوق روزانه: {fmt(emp.get('daily_salary') or 0)} ریال",
                            10, color=T()['muted'], no_wrap=True, overflow=ft.TextOverflow.ELLIPSIS),
                        txt(f"📱 {emp.get('mobile') or '-'} • 🏢 {emp.get('contract_type') or '-'}",
                            10, color=T()['muted'], no_wrap=True, overflow=ft.TextOverflow.ELLIPSIS),
                    ], spacing=2, expand=True),
                    ft.Container(txt(f"#{emp.get('personnel_code') or emp['id']}", 9, color=T()['muted']),
                                 padding=pad_sym(4, 0)),
                ], spacing=10, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                padding=pad_sym(10, 8), bgcolor=T()['card'], border_radius=12,
                border=border_all(1, T()['line']),
                on_click=lambda ev, person=emp: self.emp_detail(person))

        def fill(e=None):
            holder.controls.clear()
            q = (state['q'] or '').strip().lower()
            vis = []
            for emp in c['employees']:
                full = (f"{emp.get('first_name','')} {emp.get('last_name','')} "
                        f"{emp.get('national_code','')} {emp['id']} {emp.get('job_title','')} "
                        f"{emp.get('mobile','')} {emp.get('personnel_code','')}").lower()
                if not _match_words(full, state['q']): continue
                if state['dept'] and str(emp.get('dept_id') or '') != str(state['dept']): continue
                if state['status'] == 'active' and not emp.get('is_active'): continue
                if state['status'] == 'inactive' and emp.get('is_active'): continue
                vis.append(emp)
            sk = state['sort']
            if sk == 'name': vis.sort(key=lambda x: (x.get('last_name') or '', x.get('first_name') or ''))
            elif sk == 'salary_desc': vis.sort(key=lambda x: x.get('daily_salary') or 0, reverse=True)
            elif sk == 'salary_asc': vis.sort(key=lambda x: x.get('daily_salary') or 0)
            elif sk == 'date_desc': vis.sort(key=lambda x: x.get('employment_date') or '', reverse=True)
            elif sk == 'date_asc': vis.sort(key=lambda x: x.get('employment_date') or '')
            elif sk == 'code': vis.sort(key=lambda x: x.get('personnel_code') or str(x['id']))
            for n_, emp in enumerate(vis, 1): holder.controls.append(row_for(emp, n_))
            if not vis: holder.controls.append(self.empty('پرسنلی یافت نشد', _ic('PEOPLE_OUTLINE')))
            holder.controls.append(ft.Container(height=80))
            count_holder.content = badge(f'تعداد: {len(vis)}', T()['primary'], '#ffffff', 10)
            try: holder.update(); count_holder.update()
            except Exception: pass

        fill()
        self.set_fab(_ic('PERSON_ADD'), lambda e: self.emp_form(None))
        return ft.Column([
            card(ft.Column([
                ft.Row([txt('پرسنل', 14, True, expand=True), count_holder]),
                tf('جستجو...', on_change=lambda e: (state.update({'q': e.control.value or ''}), self.debounce('emp_q', fill)),
                   prefix=_ic('SEARCH'), size=12),
                ft.Row([
                    dd('واحد', [('', 'همه')] + [(d['id'], d['title']) for d in c['departments']],
                       '', lambda e: (state.update({'dept': e.control.value or ''}), fill()),
                       expand=True, size=11),
                    dd('وضعیت', [('', 'همه'), ('active', 'فعال'), ('inactive', 'غیرفعال')],
                       'active', lambda e: (state.update({'status': e.control.value or ''}), fill()),
                       expand=True, size=11),
                ], spacing=6),
                dd('مرتب‌سازی', [
                    ('name', '🔤 الفبایی'), ('code', '🔢 کد پرسنلی'),
                    ('salary_desc', '💰 حقوق (زیاد به کم)'), ('salary_asc', '💰 حقوق (کم به زیاد)'),
                    ('date_desc', '📅 استخدام (جدید)'), ('date_asc', '📅 استخدام (قدیم)'),
                ], 'name', lambda e: (state.update({'sort': e.control.value or 'name'}), fill()), size=11),
            ], spacing=6), padding=10),
            holder,
        ], expand=True, spacing=6)

    def v_attendance(self):
        """کارکرد پرسنل؛ اسکرول عمودی مشترک و هماهنگ‌سازی افقی محدودشده."""
        # Stale scroll callbacks must never control widgets after this view is replaced.
        attendance_generation = int(getattr(self, "_view_generation", 0))
        # ═══════════════════ Data ═══════════════════
        c = {'employees': self.db.q(
                "SELECT * FROM employees WHERE company_id=? AND is_active=1 ORDER BY id",
                (self.cid,)),
             'departments': self.db.q(
                "SELECT * FROM departments WHERE company_id=?", (self.cid,)),
             'attendances': self.db.q(
                "SELECT * FROM attendances WHERE company_id=? AND year=? AND month=?",
                (self.cid, self.year, self.month))}
        employees = [e for e in c['employees'] if e.get('is_active')]
        # Build the search index once; do not concatenate every employee's fields on each keystroke.
        employee_search = {
            e['id']: (f"{e.get('first_name','')} {e.get('last_name','')} "
                      f"{e.get('national_code','')} {e['id']} {e.get('mobile','')} "
                      f"{e.get('personnel_code','')} {e.get('job_title','')}").casefold()
            for e in employees
        }
        rates = self.db.q(
            "SELECT * FROM rate_years WHERE company_id=? AND year<=? "
            "ORDER BY year DESC LIMIT 1",
            (self.cid, self.year))
        shift_def = 0
        att_map = {a['emp_id']: a for a in c['attendances']
                   if a['year'] == self.year and a['month'] == self.month}

        # ═══════════════════ State + Refs ═══════════════════
        state = {'q': '', 'dept': '', 'sheet': False}
        inputs = {}
        ui = {'focus_emp': None, 'pos': -99}
        refs = {'names': {}, 'nums': {}}

        FIELDS = ('work_days', 'overtime_hours', 'overtime_minutes',
                  'night_hours', 'night_minutes', 'absent_hours',
                  'absent_minutes', 'mission_days', 'shift_percent',
                  'friday_hours', 'holiday_hours',
                  'friday_rest_replaced', 'holiday_rest_replaced')

        # ═══════════════════ گروه‌بندی ستون‌ها ═══════════════════
        GROUPS = [
            ('روزهای مزد', [('work_days', 'روز مزد', 60)]),
            ('اضافه کاری', [('overtime_hours', 'ساعت', 56),
                            ('overtime_minutes', 'دقیقه', 56)]),
            ('شب کاری',    [('night_hours', 'ساعت', 56),
                            ('night_minutes', 'دقیقه', 56)]),
            ('کسر کار',    [('absent_hours', 'ساعت', 56),
                            ('absent_minutes', 'دقیقه', 56)]),
            ('مأموریت',    [('mission_days', 'روز', 66)]),
            ('نوبت',       [('shift_percent', 'درصد', 58)]),
            ('جمعه',       [('friday_hours', 'ساعت', 56)]),
            ('تعطیل',      [('holiday_hours', 'ساعت', 56)]),
            ('استراحت جایگزین', [('friday_rest_replaced', 'جمعه ۰/۱', 64),
                                 ('holiday_rest_replaced', 'تعطیل ۰/۱', 64)]),
        ]
        COLS_FLAT = [(k, w) for _, subs in GROUPS for k, _, w in subs]

        # ═══════════════════ ابعاد ═══════════════════
        NAME_W, ROW_H, HEAD_H, H_HALF = 134, 38, 52, 26
        ROW_GAP, COL_GAP, OUTER_GAP = 3, 2, 4
        COLS_W = sum(w for _, w in COLS_FLAT) + len(COLS_FLAT) * COL_GAP + 4

        # ═══════════════════ پالت ═══════════════════
        P, A = T()['primary'], T()['accent']
        CARD, LINE, MUTED = T()['card'], T()['line'], T()['muted']
        SOFT = alpha(P, 0x08)

        def shadow(blur=8, y=2, op=0x18):
            try:
                return [ft.BoxShadow(blur_radius=blur, spread_radius=0,
                                    color=alpha('#000000', op),
                                    offset=ft.Offset(0, y))]
            except Exception:
                return None

        # ═══════════════════ Shared vertical viewport ═══════════════════
        # The names and numeric columns are ordinary (non-scrollable) Columns inside
        # one outer vertical ScrollView. One gesture moves BOTH columns by the same native
        # Flutter offset. The employee column stays frozen during horizontal data browsing.
        names_body = ft.Column(spacing=ROW_GAP, tight=True, width=NAME_W)
        nums_body = ft.Column(spacing=ROW_GAP, tight=True, width=COLS_W)
        body_scroll = ft.Column([], spacing=0, scroll=ft.ScrollMode.AUTO, expand=True)
        try:
            if hasattr(body_scroll, 'scroll_interval'):
                body_scroll.scroll_interval = 24  # notifications only drive batched loading
        except Exception:
            pass
        stats_holder = ft.Container()
        BATCH_SIZE = 10
        ROW_STEP = ROW_H + ROW_GAP
        scroll_state = {
            'shown': [], 'loaded': 0, 'loading': False, 'spacer': False,
            'last_batch_at': 0.0,
        }

        # ═══════════════════ Highlight ═══════════════════
        def highlight(emp_id):
            prev = ui['focus_emp']
            if prev == emp_id:
                return

            def apply(eid, color, border=None):
                for d in refs.values():
                    r = d.get(eid)
                    if r is not None:
                        try:
                            r.bgcolor = color
                            if border is not None:
                                r.border = border
                            r.update()
                        except Exception:
                            pass

            if prev is not None:
                r = refs['nums'].get(prev)
                base_bg = r.data['bg'] if r else CARD
                apply(prev, base_bg, border_all(1, LINE))
            if emp_id is not None:
                apply(emp_id, alpha(P, 0x22), border_all(1, alpha(P, 0x80)))
            ui['focus_emp'] = emp_id

        # ═══════════════════ Helpers ═══════════════════
        def cell_value(emp_id, fname, default=0):
            key = (emp_id, fname)
            if key in inputs:
                return inputs[key]
            v = att_map.get(emp_id, {}).get(fname, default)
            if v in (None, 0):
                return ""
            return f"{v:g}" if isinstance(v, float) else str(v)

        def visible_employees():
            out = []
            for emp in employees:
                full = employee_search.get(emp['id'], '')
                if not _match_words(full, state['q']):
                    continue
                if state['dept'] and str(emp.get('dept_id') or '') != str(state['dept']):
                    continue
                out.append(emp)
            return out

        # ═══════════════════ Field ═══════════════════
        def num_field(emp, fname, default=0):
            key = (emp['id'], fname)
            raw = cell_value(emp['id'], fname, default)
            filled = raw != ""

            def on_change(e, k=key, initial=raw):
                # Store every keystroke locally. Only send an extra style update when the
                # field crosses empty/non-empty; never round-trip the UI on each character.
                previous = inputs.get(k, initial)
                current = e.control.value or ''
                inputs[k] = current
                if bool(previous) != bool(current):
                    try:
                        e.control.color = P if current else T()['text']
                        e.control.weight = (ft.FontWeight.BOLD if current
                                            else ft.FontWeight.NORMAL)
                        e.control.update()
                    except Exception:
                        pass

            def on_focus(e, eid=emp['id']):
                # The focused TextField is already inside the one shared scroll viewport.
                # Do not issue scroll_to calls: they used to race each other and were not
                # awaited in older builds, producing the exact lag reported by the user.
                highlight(eid)  # highlight() also owns the focus_emp state transition

            return K(ft.TextField,
                     value=raw, dense=True, text_size=13,
                     text_align=ft.TextAlign.CENTER,
                     keyboard_type=ft.KeyboardType.NUMBER,
                     content_padding=pad_sym(2, 4),
                     color=P if filled else T()['text'],
                     weight=(ft.FontWeight.BOLD if filled
                             else ft.FontWeight.NORMAL),
                     bgcolor='transparent',
                     border=(ft.NoInputBorder() if hasattr(ft, 'NoInputBorder')
                             else ft.InputBorder.NONE),
                     on_change=on_change,
                     on_focus=on_focus,
                     height=32)

        # ═══════════════════ Rows ═══════════════════
        def name_row(emp, idx):
            is_even = (idx % 2 == 0)
            bg = CARD if is_even else SOFT
            bd = LINE if is_even else alpha(P, 0x1A)
            has_data = emp['id'] in att_map

            avatar = ft.Container(
                content=ft.Text((emp.get('first_name') or '?')[:1], size=12,
                                weight=ft.FontWeight.BOLD,
                                color='#ffffff' if has_data else P),
                width=28, height=28,
                bgcolor=P if has_data else alpha(A, 0x66),
                border=border_all(2, alpha(P, 0x30 if has_data else 0x18)),
                border_radius=14, alignment=center(),
                shadow=shadow(4, 1, 0x10))

            c = ft.Container(
                content=ft.Row([
                    txt(str(idx + 1), 7, color=MUTED, width=14,
                        align=ft.TextAlign.CENTER),
                    avatar,
                    ft.Column([
                        txt(f"{emp.get('first_name','')} {emp.get('last_name','')}",
                            11, True, no_wrap=True,
                            overflow=ft.TextOverflow.ELLIPSIS),
                        txt(f"#{emp.get('personnel_code') or emp['id']}",
                            9, color=MUTED),
                    ], spacing=0, expand=True, tight=True),
                ], spacing=6, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                width=NAME_W, height=ROW_H, padding=pad_sym(2, 6),
                bgcolor=bg,
                border=border_all(1, bd),
                border_radius=10,
                )
            c.data = {'bg': bg}
            refs['names'][emp['id']] = c
            return c

        def nums_row(emp, idx):
            is_even = (idx % 2 == 0)
            bg = CARD if is_even else SOFT
            bd = LINE if is_even else alpha(P, 0x1A)
            cells = []
            for fname, w in COLS_FLAT:
                default = shift_def if fname == 'shift_percent' else 0
                cells.append(ft.Container(
                    content=num_field(emp, fname, default),
                    width=w, height=ROW_H - 6, alignment=center(),
                    padding=pad_sym(0, 2),
                    bgcolor=SOFT if is_even else alpha(P, 0x0D),
                    border_radius=7))
            c = ft.Container(
                content=ft.Row(cells, spacing=COL_GAP,
                               vertical_alignment=ft.CrossAxisAlignment.CENTER),
                height=ROW_H, width=COLS_W, padding=pad_sym(3, 3),
                bgcolor=bg, border=border_all(1, bd), border_radius=10,
                )
            c.data = {'bg': bg}
            refs['nums'][emp['id']] = c
            return c

        # ═══════════════════ Header ═══════════════════
        def group_cell(title, subs):
            total_w = sum(w for _, _, w in subs) + (len(subs) - 1) * COL_GAP
            top = ft.Container(
                content=txt(title, 11, True, '#ffffff'),
                height=H_HALF, alignment=center(), bgcolor=P)
            if len(subs) == 1:
                bot = ft.Container(
                    content=txt(subs[0][1], 10, True, '#ffffff'),
                    height=H_HALF, alignment=center(),
                    bgcolor=alpha(P, 0xC0))
                inner = ft.Column([top, bot], spacing=1, tight=True)
            else:
                sub_cells = [ft.Container(
                    content=txt(lbl, 10, True, '#ffffff'),
                    width=w, height=H_HALF, alignment=center(),
                    bgcolor=alpha(P, 0xC0))
                    for _, lbl, w in subs]
                inner = ft.Column([top, ft.Row(sub_cells, spacing=COL_GAP)],
                                  spacing=1, tight=True)
            return ft.Container(
                content=inner, width=total_w, height=HEAD_H,
                border_radius=10, clip_behavior=ft.ClipBehavior.ANTI_ALIAS,
                shadow=shadow(6, 2, 0x20))

        def build_nums_header():
            cells = [group_cell(t, subs) for t, subs in GROUPS]
            return ft.Row(cells, spacing=COL_GAP, height=HEAD_H)

        name_header = ft.Container(
            content=ft.Row([
                ft.Icon(_ic('PERSON'), size=14, color='#ffffff'),
                txt('پرسنل', 12, True, '#ffffff'),
            ], spacing=5, alignment=ft.MainAxisAlignment.CENTER),
            width=NAME_W, height=HEAD_H,
            bgcolor=P, border_radius=10,
            shadow=shadow(6, 2, 0x20),
            alignment=center())

        # ═══════════════════ Shared vertical scroll + batched rows ═══════════════════
        TABLE_W = NAME_W + COLS_W + OUTER_GAP

        def append_next_batch(limit=None, push_update=False):
            """Append paired name/number rows into one shared vertical scroll surface."""
            if scroll_state['loading']:
                return 0
            shown = scroll_state['shown']
            begin = scroll_state['loaded']
            if begin >= len(shown):
                return 0
            scroll_state['loading'] = True
            try:
                # The last pair of controls reserves the height of not-yet-built rows.
                # This keeps the scrollbar extent stable without creating hundreds of
                # TextFields at startup; actual rows are materialized before reaching them.
                if scroll_state['spacer']:
                    try:
                        names_body.controls.pop()
                        nums_body.controls.pop()
                    except Exception:
                        pass
                    scroll_state['spacer'] = False

                count = int(limit or BATCH_SIZE)
                stop = min(len(shown), begin + max(1, count))
                for idx in range(begin, stop):
                    emp = shown[idx]
                    # Same row index, height and spacing in both columns; vertical motion
                    # is inherited from body_scroll, never copied through scroll_to.
                    names_body.controls.append(name_row(emp, idx))
                    nums_body.controls.append(nums_row(emp, idx))
                scroll_state['loaded'] = stop
                remaining = max(0, len(shown) - stop)
                if remaining:
                    reserved_height = max(0, remaining * ROW_STEP - ROW_GAP)
                    names_body.controls.append(ft.Container(
                        height=reserved_height, width=NAME_W))
                    nums_body.controls.append(ft.Container(
                        height=reserved_height, width=COLS_W))
                    scroll_state['spacer'] = True
                if push_update:
                    try:
                        # Send both dirty columns in the same Flet update cycle.
                        self.page.update()
                    except Exception:
                        try:
                            names_body.update()
                            nums_body.update()
                        except Exception:
                            pass
                return stop - begin
            finally:
                scroll_state['loading'] = False

        def _maybe_load_more(e):
            if scroll_state['loading'] or scroll_state['loaded'] >= len(scroll_state['shown']):
                return False
            try:
                # extent_after includes the reserved spacer, so use the absolute vertical
                # position + viewport size to detect when unbuilt rows are approaching.
                pixels = max(0.0, float(getattr(e, 'pixels', 0.0) or 0.0))
                inside = getattr(e, 'extent_inside', None)
                if inside is None or float(inside or 0) <= 0:
                    try:
                        inside = max(240.0, float(self.page.height or 800) - 380.0)
                    except Exception:
                        inside = 420.0
                viewport_end = pixels + max(0.0, float(inside))
                materialized_end = max(0, scroll_state['loaded']) * ROW_STEP
                near_end = viewport_end >= materialized_end - ROW_STEP * 5
            except Exception:
                near_end = False
            if not near_end:
                return False
            now = time.monotonic()
            if now - float(scroll_state.get('last_batch_at', 0.0)) < 0.10:
                return False
            scroll_state['last_batch_at'] = now
            return bool(append_next_batch(push_update=True))

        def on_body_scroll(e):
            _maybe_load_more(e)

        body_scroll.on_scroll = on_body_scroll

        # ═══════════════════ Rebuild ═══════════════════
        def rebuild(e=None):
            shown = visible_employees()
            scroll_state.update({
                'shown': shown, 'loaded': 0, 'loading': False,
                'spacer': False, 'last_batch_at': 0.0,
            })
            names_body.controls.clear()
            nums_body.controls.clear()
            refs['names'].clear()
            refs['nums'].clear()
            ui['focus_emp'] = None

            if shown:
                # Build a modest first page; more rows are appended only near the end.
                try:
                    page_h = float(self.page.height or 800)
                except Exception:
                    page_h = 800.0
                # Prefill beyond the estimated viewport; otherwise a tall desktop page
                # could have no scrollbar yet and never request the next batch.
                initial = max(12, min(50, int(max(0.0, page_h - 270) // ROW_STEP) + 4))
                append_next_batch(limit=initial, push_update=False)
            else:
                names_body.controls.append(ft.Container(
                    content=txt("پرسنلی یافت نشد", 11, True, MUTED,
                                align=ft.TextAlign.CENTER),
                    width=NAME_W, height=ROW_H, alignment=center(),
                    border=border_all(1, LINE), border_radius=10))
                nums_body.controls.append(ft.Container(
                    content=txt("برای این فیلتر پرسنلی وجود ندارد", 11, color=MUTED),
                    width=COLS_W, height=ROW_H, alignment=center()))

            reg = sum(1 for emp in shown if emp['id'] in att_map)
            rem = len(shown) - reg
            pct = (reg / len(shown)) if shown else 0
            stats_holder.content = ft.Column([
                ft.Row([
                    badge(f"کل {len(shown)}", P, '#ffffff', 10),
                    badge(f"✓ {reg}", '#dbeafe', '#1d4ed8', 10),
                    badge(f"◯ {rem}", '#fef3c7', '#92400e', 10),
                    ft.Container(expand=True),
                    badge(f"{MONTHS[self.month-1]} {self.year}", A, P, 10),
                ], spacing=6),
                ft.Container(
                    ft.ProgressBar(value=pct, height=4, color=P,
                                   bgcolor=alpha(P, 0x20)),
                    border_radius=2),
            ], spacing=5)
            try:
                # A single diff/update keeps both columns and the counters in agreement.
                self.page.update()
            except Exception:
                try:
                    names_body.update()
                    nums_body.update()
                    stats_holder.update()
                except Exception:
                    pass

        # ═══════════════════ Actions ═══════════════════
        def save_all(e=None):
            dim = days_in_month(self.year, self.month)
            errors, staged = [], []
            for emp in employees:
                touched = any((emp['id'], f) in inputs for f in FIELDS)
                if emp['id'] not in att_map and not touched:
                    continue

                def n(fname, default=0, emp=emp):
                    key = (emp['id'], fname)
                    if key in inputs:
                        return parse_float(inputs[key])
                    return parse_float(att_map.get(emp['id'], {}).get(fname, default))

                work = n('work_days')
                ot_h = n('overtime_hours'); ot_m = n('overtime_minutes')
                ng_h = n('night_hours');    ng_m = n('night_minutes')
                ab_h = n('absent_hours');   ab_m = n('absent_minutes')
                mission = n('mission_days'); shift = n('shift_percent', shift_def)
                friday = n('friday_hours'); holiday = n('holiday_hours')
                fr = n('friday_rest_replaced'); hr = n('holiday_rest_replaced')
                label = f"{emp.get('first_name','')} {emp.get('last_name','')}"

                if work < 0 or work > dim:
                    errors.append(f"{label}: روز ۰-{dim}"); continue
                if not (0 <= ot_m <= 59 and 0 <= ng_m <= 59 and 0 <= ab_m <= 59):
                    errors.append(f"{label}: دقیقه ۰-۵۹"); continue
                if min(ot_h, ng_h, ab_h, mission, shift, friday, holiday,
                       fr, hr) < 0:
                    errors.append(f"{label}: منفی مجاز نیست"); continue
                if mission > dim or shift > 100:
                    errors.append(f"{label}: خارج از محدوده"); continue
                if fr not in (0, 1) or hr not in (0, 1):
                    errors.append(f"{label}: استراحت جایگزین ۰/۱"); continue

                staged.append(dict(
                    emp_id=emp['id'], year=self.year, month=self.month,
                    work_days=work, overtime_hours=ot_h,
                    overtime_minutes=ot_m, night_hours=ng_h,
                    night_minutes=ng_m, absent_hours=ab_h,
                    absent_minutes=ab_m, mission_days=mission,
                    shift_percent=shift, friday_hours=friday,
                    holiday_hours=holiday,
                    friday_rest_replaced=int(fr),
                    holiday_rest_replaced=int(hr)))

            if errors:
                self.info('بررسی', 'ذخیره نشد:\n\n' + '\n'.join(errors[:15]))
                return
            self.db.upsert_attendances(self.cid, staged)
            for rec in staged:
                # Keep the in-memory view/cache aligned with SQLite without rebuilding tabs.
                att_map[rec['emp_id']] = dict(rec)
            inputs.clear()
            rebuild()
            self.toast(f'✅ {len(staged)} رکورد ذخیره شد.')

        def copy_prev(e=None):
            py, pm = ((self.year, self.month - 1)
                      if self.month > 1 else (self.year - 1, 12))
            ids = {emp['id'] for emp in employees}
            prev = [a for a in self.db.q(
                        "SELECT * FROM attendances WHERE company_id=? AND year=? AND month=?",
                        (self.cid, py, pm)) if a['emp_id'] in ids]
            if not prev:
                self.toast('ماه قبل اطلاعاتی ندارد.', True)
                return

            def go():
                copied = [dict(a, year=self.year, month=self.month) for a in prev]
                self.db.upsert_attendances(self.cid, copied)
                for rec in copied:
                    att_map[rec['emp_id']] = dict(rec)
                inputs.clear()
                rebuild()
                self.toast(f'✅ {len(prev)} رکورد کپی شد.')
            self.confirm(f'کارکرد {len(prev)} نفر از ماه قبل کپی شود؟',
                         go, 'کپی', False)

        def clear_month(e=None):
            def go():
                with self.db.tx() as conn:
                    conn.execute(
                        "DELETE FROM attendances WHERE company_id=? AND year=? AND month=?",
                        (self.cid, self.year, self.month))
                inputs.clear()
                att_map.clear()
                rebuild()
                self.toast('🗑 کارکرد ماه پاک شد')
            self.confirm(f"همه کارکرد {MONTHS[self.month-1]} {self.year} پاک شود؟",
                         go, 'حذف')

        def export_sheet(e=None):
            try:
                path = export_attendance_csv(self.db, self.cid, self.year,
                                             self.month, employees, att_map)
                self.file_dialog(path, "✅ CSV کارکرد ساخته شد")
            except Exception as ex:
                self.info("خطا", str(ex))

        def fill_all(e=None):
            dim = days_in_month(self.year, self.month)
            for emp in employees:
                inputs[(emp['id'], 'work_days')] = str(dim)
            rebuild()
            self.toast(f"✅ {dim} روز برای همه پر شد")

        def fill_shift_default(e=None):
            rate_row = rates[0] if rates else {}
            shift_rates = {
                'morning_evening': _as_float(rate_row.get('shift_morning_evening'), 10),
                'morning_evening_night': _as_float(rate_row.get('shift_three_turn'), 15),
                'morning_night': _as_float(rate_row.get('shift_morning_night'), 22.5),
                'evening_night': _as_float(rate_row.get('shift_morning_night'), 22.5),
                'none': 0.0,
            }
            for emp in employees:
                pattern = emp.get('shift_pattern') or 'none'
                inputs[(emp['id'], 'shift_percent')] = str(
                    shift_rates.get(pattern, 0.0))
            rebuild()
            self.toast('✅ درصد نوبت مطابق الگوی هر پرسنل پر شد')

        def clear_inputs(e=None):
            inputs.clear()
            rebuild()
            self.toast("🔄 فرم پاک شد")

        def change_year(e):
            y = parse_int(e.control.value)
            if 1300 <= y <= 1500 and y != self.year:
                self.year = y
                self.refresh()

        def change_month(e):
            self.month = int(e.control.value)
            self.refresh()

        def on_search(e):
            state['q'] = e.control.value or ''
            # Short debounce keeps search responsive without rebuilding for every keystroke.
            self.debounce('att_q', rebuild, delay=0.12)

        def on_dept(e):
            state['dept'] = e.control.value or ''
            rebuild()

        # ═══════════════════ Init ═══════════════════
        rebuild()

        # ═══════════════════ Top Bar Helper ═══════════════════
        def icon_btn(icon, color, handler, tip):
            return ft.Container(
                content=ft.Icon(icon, color='#ffffff', size=20),
                bgcolor=color, width=42, height=42, alignment=center(),
                border_radius=10, shadow=shadow(6, 2, 0x28),
                on_click=handler, ink=True, tooltip=tip)

        # ابتدا فقط ظرف پنل را می‌سازیم؛ محتوای دکمه‌ها پایین‌تر و پس از تعریف
        # action_tile به آن متصل می‌شود. ساخت کامل پنل در این نقطه باعث NameError می‌شد.
        panel_inner = ft.Container(
            content=ft.Column([], spacing=8, tight=True, scroll=ft.ScrollMode.AUTO),
            bgcolor=CARD, border_radius=20,
            shadow=shadow(24, 8, 0x55), padding=16)

        # ── Container بیرونی که موقعیت + مخفی‌بودن را کنترل می‌کند ──
        sheet = ft.Container(
            content=panel_inner,
            left=0, right=0, bottom=0,
            visible=False)

        # Dimmer
        dimmer = ft.Container(
            bgcolor='#00000070',
            left=0, right=0, top=0, bottom=0,
            visible=False)

        # ═══════════════════ Toggle Sheet (بعد از تعریف sheet و dimmer) ═══════════════════
        def toggle_sheet(e=None):
            state['sheet'] = not state['sheet']
            try:
                dimmer.visible = state['sheet']
                sheet.visible = state['sheet']
                dimmer.update()
                sheet.update()
            except Exception:
                pass

        def close_sheet(e=None):
            if state['sheet']:
                toggle_sheet()

        # اتصال on_click به dimmer بعد از تعریف toggle_sheet
        try:
            dimmer.on_click = toggle_sheet
        except Exception:
            pass

        # ═══════════════════ Action Tile ═══════════════════
        def action_tile(icon, label, sub, color, handler):
            return ft.Container(
                content=ft.Column([
                    ft.Container(
                        ft.Icon(icon, color='#ffffff', size=20),
                        width=40, height=40, bgcolor=color,
                        border_radius=10, alignment=center(),
                        shadow=shadow(4, 2, 0x30)),
                    txt(label, 11, True, T()['text'],
                        align=ft.TextAlign.CENTER),
                    txt(sub, 8, color=MUTED, align=ft.TextAlign.CENTER),
                ], spacing=4, tight=True,
                   horizontal_alignment=ft.CrossAxisAlignment.CENTER),
                padding=pad_sym(6, 10),
                border_radius=12,
                bgcolor=alpha(color, 0x12),
                border=border_all(1, alpha(color, 0x33)),
                ink=True, on_click=handler, expand=True)

        # محتوای پنل پس از تعریف action_tile ساخته می‌شود.
        panel_inner.content = ft.Column([
            ft.Container(
                ft.Container(width=42, height=4,
                             bgcolor=alpha(P, 0x55), border_radius=2),
                alignment=center()),
            ft.Row([
                ft.Container(
                    ft.Icon(_ic('TUNE'), color='#ffffff', size=16),
                    width=32, height=32, bgcolor=P,
                    border_radius=8, alignment=center()),
                ft.Column([
                    txt("پنل کنترل کارکرد", 13, True),
                    txt(f"{MONTHS[self.month-1]} {self.year}",
                        9, color=MUTED),
                ], spacing=0, expand=True),
                ft.IconButton(_ic('CLOSE'), on_click=toggle_sheet,
                              icon_color=MUTED, icon_size=18,
                              tooltip='بستن'),
            ], spacing=8,
               vertical_alignment=ft.CrossAxisAlignment.CENTER),
            ft.Divider(height=1, color=LINE),

            dd("واحد سازمانی",
               [('', 'همه واحدها')] + [(d['id'], d['title'])
                                       for d in c['departments']],
               state['dept'], on_dept, size=12),

            ft.Divider(height=1, color=LINE),
            txt("⚡ عملیات سریع", 11, True, P),

            ft.Row([
                action_tile(_ic('SAVE'), 'ذخیره', 'کارکرد ماه',
                            '#047857',
                            lambda e: (close_sheet(), save_all())),
                action_tile(_ic('BOLT'), 'تکمیل روز', 'همه پرسنل',
                            '#0891b2',
                            lambda e: (fill_all(), close_sheet())),
            ], spacing=6),

            ft.Row([
                action_tile(_ic('CONTENT_COPY'), 'کپی ماه قبل',
                            'از ماه گذشته', '#7c3aed',
                            lambda e: (close_sheet(), copy_prev())),
                action_tile(_ic('PERCENT'), 'نوبت پیش‌فرض',
                            'از الگوی پرسنل', '#d97706',
                            lambda e: (fill_shift_default(), close_sheet())),
            ], spacing=6),

            ft.Row([
                action_tile(_ic('DOWNLOAD'), 'CSV', 'خروجی اکسل',
                            P,
                            lambda e: (close_sheet(), export_sheet())),
                action_tile(_ic('REFRESH'), 'پاک فرم', 'بازنشانی',
                            '#64748b',
                            lambda e: (clear_inputs(), close_sheet())),
                action_tile(_ic('DELETE'), 'حذف ماه', 'کل کارکرد',
                            '#c0392b',
                            lambda e: (close_sheet(), clear_month())),
            ], spacing=6),

            ft.Container(height=6),
        ], spacing=8, tight=True, scroll=ft.ScrollMode.AUTO)

        # ═══════════════════ Top Bar ═══════════════════
        top_bar = ft.Container(
            content=ft.Column([
                ft.Row([
                    tf("سال", self.year, kb=True, width=80, size=13,
                       on_change=change_year),
                    dd("ماه", [(i + 1, m) for i, m in enumerate(MONTHS)],
                       self.month, change_month, expand=True, size=13),
                    icon_btn(_ic('SAVE'), T()['success'], save_all, 'ذخیره'),
                    icon_btn(_ic('TUNE'), P, toggle_sheet, 'پنل کنترل'),
                ], spacing=6, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                tf("جستجوی پرسنل...", value=state['q'],
                   on_change=on_search, prefix=_ic('SEARCH'), size=13),
            ], spacing=6, horizontal_alignment=ft.CrossAxisAlignment.STRETCH),
            padding=pad_sym(8, 10))

        # ═══════════════════ Stats Bar ═══════════════════
        stats_bar = ft.Container(stats_holder, padding=pad_sym(6, 12))

        # ═══════════════════ Table layout ═══════════════════
        # Only horizontal scrolling is mirrored (header <-> numeric cells). Vertical
        # scrolling belongs to body_scroll and contains BOTH columns as one child row.
        header_nums_hscroll = ft.Row(
            [build_nums_header()], scroll=ft.ScrollMode.AUTO, expand=True,
            vertical_alignment=ft.CrossAxisAlignment.STRETCH)
        nums_hscroll = ft.Row(
            [nums_body], scroll=ft.ScrollMode.AUTO, expand=True,
            vertical_alignment=ft.CrossAxisAlignment.STRETCH)
        for _horizontal in (header_nums_hscroll, nums_hscroll):
            try:
                if hasattr(_horizontal, 'scroll_interval'):
                    # Scroll events are notifications, not a frame-by-frame RPC stream.
                    _horizontal.scroll_interval = 75
            except Exception:
                pass

        body_row = ft.Row(
            [names_body, nums_hscroll],
            spacing=OUTER_GAP,
            vertical_alignment=ft.CrossAxisAlignment.STRETCH,
        )
        body_scroll.controls = [body_row]

        # Horizontal offsets are synchronized safely with awaited scroll_to. This is only
        # a horizontal-header alignment helper; vertical position is never synchronized in code.
        h_sync = {
            'target': -99999.0,
            'header': -99999.0,
            'body': -99999.0,
            'busy': False,
            'pending': None,
            'last_send': 0.0,
        }
        H_SYNC_MIN_INTERVAL = 0.12  # максимум ~8 программных прокруток в секунду

        def _attendance_view_is_current():
            try:
                return (
                    int(getattr(self, '_view_generation', -1)) == attendance_generation
                    and bool(self.stack)
                    and self.stack[-1][0] == self.TABS[2]
                )
            except Exception:
                return False

        async def _drain_horizontal_sync():
            """Single-flight sync: coalesce many scroll events into the latest offset.

            Flet's scroll_to is a client/server async operation. Sending a call for every
            scroll event creates a backlog; if navigation removes the target control before
            those replies arrive, Flet Web logs 'Control ID is not registered'.
            """
            if h_sync['busy']:
                return
            h_sync['busy'] = True
            try:
                while h_sync['pending'] is not None and _attendance_view_is_current():
                    source, offset = h_sync['pending']
                    h_sync['pending'] = None
                    wait_for = H_SYNC_MIN_INTERVAL - (time.monotonic() - h_sync['last_send'])
                    if wait_for > 0:
                        await asyncio.sleep(wait_for)
                    # During the throttle delay a newer event may arrive; always use it.
                    if h_sync['pending'] is not None:
                        source, offset = h_sync['pending']
                        h_sync['pending'] = None
                    if not _attendance_view_is_current():
                        break
                    source_key = 'header' if source == 'header' else 'body'
                    if abs(offset - float(h_sync[source_key])) < 1.0:
                        continue
                    if abs(offset - float(h_sync['target'])) < 1.0:
                        h_sync[source_key] = offset
                        continue
                    target = nums_hscroll if source == 'header' else header_nums_hscroll
                    h_sync['target'] = offset
                    h_sync['last_send'] = time.monotonic()
                    # Use one in-flight client method at a time; skip work after navigation.
                    await _await_if(target.scroll_to(offset=offset, duration=0))
                    if not _attendance_view_is_current():
                        break
                    h_sync[source_key] = offset
            except Exception:
                # Connection close / control disposal during navigation is not fatal.
                # Do not call update() on stale controls from this handler.
                pass
            finally:
                h_sync['busy'] = False
                # Event handlers can enqueue the newest offset while we were awaiting.
                if h_sync['pending'] is not None and _attendance_view_is_current():
                    try:
                        self.page.run_task(_drain_horizontal_sync)
                    except Exception:
                        # On older Flet versions, a future scroll event will drain it.
                        pass

        async def _sync_horizontal(source, event):
            if not _attendance_view_is_current():
                return
            try:
                offset = max(0.0, float(getattr(event, 'pixels', 0.0) or 0.0))
            except Exception:
                return
            source_key = 'header' if source == 'header' else 'body'
            # Ignore the echo event caused by our previous scroll_to() call.
            # This prevents two scroll views from repeatedly triggering one another.
            if abs(offset - float(h_sync['target'])) < 1.0:
                h_sync[source_key] = offset
                return
            # Latest-wins queue prevents dozens of concurrent scroll_to invocations.
            h_sync['pending'] = (source, offset)
            if not h_sync['busy']:
                await _drain_horizontal_sync()

        async def on_header_horizontal_scroll(e):
            await _sync_horizontal('header', e)

        async def on_body_horizontal_scroll(e):
            await _sync_horizontal('body', e)

        header_nums_hscroll.on_scroll = on_header_horizontal_scroll
        nums_hscroll.on_scroll = on_body_horizontal_scroll

        table_header = ft.Row(
            [name_header, header_nums_hscroll],
            spacing=OUTER_GAP,
            vertical_alignment=ft.CrossAxisAlignment.CENTER,
        )
        table = ft.Column([table_header, body_scroll], spacing=4, expand=True)

        # No resize-time vertical scroll_to calls: the names and value columns inherit
        # the exact same scroll position from body_scroll by construction.
        self._view_resize = lambda e=None: None

        # ═══════════════════ Return ═══════════════════
        main = ft.Column([
            top_bar,
            ft.Divider(height=1, color=LINE),
            stats_bar,
            ft.Divider(height=1, color=LINE),
            ft.Container(table, expand=True, padding=pad_sym(4, 8)),
        ], spacing=0, expand=True)

        return ft.Stack([main, dimmer, sheet], expand=True)   
    # ── حقوق ──
    def v_payroll(self):
        c = self.db.company_data(self.cid)
        emps = {e['id']: e for e in c['employees']}
        depts = {d['id']: d for d in c['departments']}
        pays_all = self.svc.payrolls(self.cid, self.year, self.month)
        st = {'q': '', 'dept': ''}
        holder = ft.ListView(spacing=4, expand=True)
        totals_holder = ft.Container()

        def toggle_payment(payroll_id, paid):
            message = _set_payroll_payment(self.db, payroll_id, paid, self.cid)
            if message:
                self.info('مدیریت پرداخت فیش', message); return
            self.toast('وضعیت پرداخت فیش به‌روزرسانی شد')
            self.refresh()

        def filtered():
            out = []
            for p in pays_all:
                e = emps.get(p['emp_id'])
                if not e: continue
                hay = (f"{e.get('first_name','')} {e.get('last_name','')} "
                       f"{e.get('national_code','')} {e['id']} {e.get('personnel_code','')}").lower()
                if not _match_words(hay, st['q']): continue
                if st['dept'] and str(e.get('dept_id') or '') != str(st['dept']): continue
                out.append(p)
            return out

        def fill():
            holder.controls.clear()
            ps = filtered()
            gross = sum(p['gross_salary'] for p in ps)
            net = sum(p['net_salary'] for p in ps)
            totals_holder.content = ft.Container(
                content=ft.Row([
                    badge(f"{len(ps)} فیش", T()['primary'], '#ffffff', 9),
                    txt(f"ناخالص {fmt(gross)}", 10, color=T()['muted']),
                    txt(f"خالص {fmt(net)}", 11, True, T()['success']),
                ], spacing=8),
                padding=pad_sym(8, 3))

            for i, p in enumerate(ps, 1):
                e = emps.get(p['emp_id']) or {}
                dept_name = (depts.get(e.get('dept_id')) or {}).get('title', '-')
                paid = p.get('payment_status') == 'paid'

                # ─── دکمه کوچک پرداخت روی کارت ───
                pay_btn = ft.Container(
                    content=ft.Row([
                        ft.Icon(_ic('UNDO' if paid else 'CHECK_CIRCLE'),
                                color='#ffffff', size=13),
                        txt('لغو' if paid else 'پرداخت', 10, True, '#ffffff'),
                    ], spacing=3, tight=True),
                    padding=pad_sym(8, 5), border_radius=8, ink=True,
                    bgcolor=T()['muted'] if paid else T()['success'],
                    on_click=lambda ev, pid=p['id'], t=(not paid): toggle_payment(pid, t))

                holder.controls.append(ft.Container(
                    content=ft.Column([
                        # ردیف ۱: شماره + نام + دکمه پرداخت
                        ft.Row([
                            badge(f"#{i}", T()['primary'], '#ffffff', 8),
                            txt(f"{e.get('first_name','')} {e.get('last_name','')}",
                                12, True, expand=True, no_wrap=True,
                                overflow=ft.TextOverflow.ELLIPSIS),
                            pay_btn,
                        ], spacing=6,
                           vertical_alignment=ft.CrossAxisAlignment.CENTER),
                        # ردیف ۲: واحد و شغل
                        txt(f"{dept_name} • {e.get('job_title') or '-'}",
                            9, color=T()['muted'], no_wrap=True,
                            overflow=ft.TextOverflow.ELLIPSIS),
                        # ردیف ۳: پایه / اضافه / مزایا
                        ft.Row([
                            txt(f"پایه {fmt(p['base_salary_monthly'])}", 9, color=T()['muted']),
                            txt(f"اضافه {fmt(p.get('overtime_amount',0))}", 9, color=T()['muted']),
                            txt(f"مزایا {fmt(p.get('benefits_sum',0))}", 9, color=T()['muted']),
                        ], spacing=6, wrap=True),
                        # ردیف ۴: بیمه / مالیات / وام / کسر
                        ft.Row([
                            txt(f"بیمه {fmt(p['insurance_emp'])}", 9, color=T()['muted']),
                            txt(f"مالیات {fmt(p['tax'])}", 9, color=T()['muted']),
                            txt(f"وام {fmt(p['loan_install'])}", 9, color=T()['muted']),
                            txt(f"کسر {fmt(p['absent_ded'])}", 9, color=T()['muted']),
                        ], spacing=6, wrap=True),
                        # ردیف ۵: روز / خالص / وضعیت
                        ft.Row([
                            badge(f"روز {p['work_days']:g}", T()['accent'], T()['primary'], 8),
                            txt(f"خالص {fmt(p['net_salary'])}", 11, True, T()['success']),
                            ft.Container(expand=True),
                            badge('✅ پرداخت شد' if paid else '⏳ پرداخت نشده',
                                  T()['success'] if paid else T()['muted'],
                                  '#ffffff', 8),
                        ], spacing=6, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    ], spacing=3),
                    padding=pad_sym(10, 7), bgcolor=T()['card'],
                    border_radius=10, border=border_all(1, T()['line']),
                    on_click=lambda ev, pid=p['id']: self.push("فیش حقوقی",
                                                              lambda: self.v_slip(pid))))

            if not ps:
                holder.controls.append(self.empty(
                    "فیشی برای این ماه نیست؛ کارکرد را ثبت و «محاسبه» را بزنید",
                    _ic("RECEIPT_LONG")))
            holder.controls.append(ft.Container(height=20))
            try: holder.update(); totals_holder.update()
            except Exception: pass

        def calc(e):
            paid_count   = sum(1 for p in pays_all if p.get('payment_status') == 'paid')
            unpaid_count = len(pays_all) - paid_count

            def go(only_unpaid):
                try:
                    n = self.svc.calculate(self.cid, self.year, self.month,
                                           only_unpaid=only_unpaid)
                except Exception as ex:
                    log_error(traceback.format_exc())
                    self.toast(f"خطا: {ex}", True); return
                self.toast("کارکردی ثبت نشده" if n == 0
                           else f"✅ {n} فیش محاسبه شد", n == 0)
                self.refresh()

            # حالت ۱: مخلوطِ پرداخت‌شده و پرداخت‌نشده
            if paid_count > 0 and unpaid_count > 0:
                self.confirm(
                    f"🔒 {paid_count} فیش پرداخت‌شده دست‌نخورده می‌ماند.\n"
                    f"♻️ {unpaid_count} فیش پرداخت‌نشده بازمحاسبه می‌شود.\n\nادامه؟",
                    lambda: go(True), "بازمحاسبه پرداخت‌نشده‌ها", False)

            # حالت ۲: همه پرداخت‌شده
            elif paid_count > 0 and unpaid_count == 0:
                self.info(
                    "همه فیش‌ها پرداخت شده",
                    "همه فیش‌های این ماه پرداخت‌شده‌اند و بازمحاسبه نمی‌شوند.\n\n"
                    "اگر واقعاً نیاز به بازمحاسبه دارید، ابتدا وضعیت پرداخت "
                    "فیش(های) موردنظر را با دکمه «لغو» روی کارت آن‌ها لغو کنید.")

            # حالت ۳: همه پرداخت‌نشده
            else:
                if pays_all:
                    self.confirm("فیش‌های قبلی بازمحاسبه می‌شوند. ادامه؟",
                                 lambda: go(False), "بازمحاسبه", False)
                else:
                    go(False)

        def delete_month(e):
            if not pays_all:
                self.toast("فیشی برای حذف نیست", True); return
            if any(p.get('payment_status') == 'paid' for p in pays_all):
                self.info('حذف فیش‌ها', 'ابتدا وضعیت پرداخت را لغو کنید.'); return
            def go():
                n = self.svc.delete_month(self.cid, self.year, self.month)
                self.toast(f"🗑 {n} فیش حذف شد"); self.refresh()
            self.confirm(f"همه فیش‌های {MONTHS[self.month-1]} {self.year} حذف شود؟", go, "حذف")

        def pdf_slips(e):
            ps = filtered()
            if not ps: self.toast("فیشی وجود ندارد", True); return
            slips = []
            for p in ps:
                # 🆕 اقساط وام هر فیش را ضمیمه می‌کنیم
                loan_insts = self.db.q("""SELECT li.*, l.principal, l.remaining_balance
                    FROM loan_installments li JOIN loans l ON l.id=li.loan_id
                    WHERE li.calculated_payroll_id=? OR li.paid_payroll_id=?""",
                    (p['id'], p['id']))
                pay_copy = dict(p)
                pay_copy['loan_insts'] = loan_insts
                slips.append(dict(pay=pay_copy,
                                  emp=emps.get(p['emp_id']),
                                  dept=depts.get((emps.get(p['emp_id']) or {}).get('dept_id')),
                                  details=self.svc.details(p['id'])))
            try:
                path = build_pdf(os.path.join(export_dir(),
                    f"payslips_{self.year}_{self.month:02d}_{datetime.now():%H%M%S}.pdf"),
                    c, slips)
                self.file_dialog(path, "📄 PDF فیش‌ها ساخته شد", len(slips))
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا", str(ex))

        def pdf_list(e):
            ps = filtered()
            if not ps: self.toast("فیشی وجود ندارد", True); return
            rows = []
            for p in ps:
                e2 = emps.get(p['emp_id']) or {}
                rows.append(dict(first_name=e2.get('first_name',''),
                                 last_name=e2.get('last_name',''),
                                 base_salary_monthly=p['base_salary_monthly'],
                                 overtime_amount=p.get('overtime_amount',0),
                                 night_amount=p.get('night_amount',0),
                                 shift_amount=p.get('shift_amount',0),
                                 friday_amount=p.get('friday_amount',0),
                                 benefits_sum=p.get('benefits_sum',0),
                                 gross_salary=p['gross_salary'],
                                 insurance_emp=p['insurance_emp'], tax=p['tax'],
                                 loan_install=p['loan_install'],
                                 absent_ded=p['absent_ded'],
                                 net_salary=p['net_salary']))
            try:
                path = os.path.join(export_dir(),
                    f"payroll_list_{self.year}_{self.month:02d}_{datetime.now():%Y%m%d_%H%M%S}.pdf")
                build_payroll_list_pdf(path, c, self.year, self.month, rows)
                self.file_dialog(path, "📋 لیست حقوق PDF ساخته شد")
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا", str(ex))

        def export_csv(e):
            try:
                path = export_full_csv(self.db, self.svc, self.cid, self.year, self.month)
                self.file_dialog(path, "✅ CSV ساخته شد")
            except Exception as ex: self.info("خطا", str(ex))

        fill()

        # ─── آیکون‌های کوچک نوار ابزار ───
        def mini(icon, handler, color, tooltip):
            return ft.Container(
                content=ft.Icon(icon, color=color, size=18),
                padding=6, border_radius=8, ink=True, tooltip=tooltip,
                on_click=handler)

        year_field = tf("سال", self.year, kb=True, width=58, size=11,
                        on_change=lambda e: (
                            (setattr(self, 'year', parse_int(e.control.value)) or self.refresh())
                            if 1300 <= parse_int(e.control.value) <= 1500 else None))
        month_field = dd("ماه", [(i+1, m) for i, m in enumerate(MONTHS)], self.month,
                         lambda e: (setattr(self, 'month', int(e.control.value)), self.refresh()),
                         width=86, size=11)
        dept_field = dd("واحد",
                        [('', 'همه')] + [(d['id'], d['title']) for d in c['departments']],
                        '', lambda e: (st.update({'dept': e.control.value or ''}), fill()),
                        expand=True, size=11)

        # ─── دکمه محاسبه بزرگ ───
        calc_btn = ft.Container(
            content=ft.Row([
                ft.Icon(_ic("CALCULATE"), color='#ffffff', size=26),
                txt("محاسبه حقوق", 16, True, '#ffffff'),
            ], spacing=10, alignment=ft.MainAxisAlignment.CENTER, tight=True),
            padding=pad_sym(20, 14), border_radius=14, ink=True,
            bgcolor=T()['success'], alignment=center(),
            on_click=calc,
            shadow=ft.BoxShadow(blur_radius=10, spread_radius=0,
                                color=alpha(T()['success'], 0x55),
                                offset=ft.Offset(0, 3)))

        top = card(ft.Column([
            # ردیف ۱: دوره و واحد
            ft.Row([year_field, month_field, dept_field], spacing=4),
            # ردیف ۲: دکمه محاسبه بزرگ
            calc_btn,
            # ردیف ۳: سرچ‌باکس بزرگ
            tf("🔍 جستجوی پرسنل...",
               on_change=lambda e: (st.update({'q': (e.control.value or '').lower().strip()}), self.debounce('pay_q', fill)),
               prefix=_ic("SEARCH"), size=14, expand=True,
               content_padding=pad_sym(14, 16)),
            # ردیف ۴: ابزارهای جانبی
            ft.Row([
                mini(_ic("PICTURE_AS_PDF"), pdf_slips,   T()['primary'], "فیش‌ها PDF"),
                mini(_ic("LIST_ALT"),       pdf_list,    T()['primary'], "لیست PDF"),
                mini(_ic("FILE_DOWNLOAD"),  export_csv,  T()['primary'], "CSV"),
                ft.Container(expand=True),
                mini(_ic("DELETE"),         delete_month,"#c0392b",      "حذف فیش‌های ماه"),
            ], spacing=4, vertical_alignment=ft.CrossAxisAlignment.CENTER),
        ], spacing=6), padding=10)

        return ft.Column([top, totals_holder, holder], expand=True, spacing=4)

    def v_slip(self, pid):
        p = self.db.q1("SELECT * FROM payrolls WHERE id=?", (pid,))
        if not p: return self.empty("فیش یافت نشد")
        c = self.db.company_data(self.cid)
        e = next((x for x in c['employees'] if x['id'] == p['emp_id']), None)
        dept = next((d for d in c['departments']
                     if d['id'] == (e or {}).get('dept_id')), None)
        dets = self.svc.details(pid)
        ben = [d for d in dets if d['type'] == 1]
        ded = [d for d in dets if d['type'] == 2 and d['amount']]
        extras = [(n, p[k]) for n, k in (("اضافه‌کاری", 'overtime_amount'),
                                          ("نوبت‌کاری", 'shift_amount'),
                                          ("شب‌کاری", 'night_amount'),
                                          ("ماموریت", 'mission_amount'),
                                          ("جمعه‌کاری", 'friday_amount'),
                                          ("تعطیل‌کاری", 'holiday_amount')) if p.get(k)]

        # 🆕 اقساط وام مرتبط با این فیش
        loan_insts = self.db.q("""SELECT li.*, l.principal, l.remaining_balance
            FROM loan_installments li JOIN loans l ON l.id=li.loan_id
            WHERE li.calculated_payroll_id=? OR li.paid_payroll_id=?""",
            (pid, pid))

        def sec(title, rows, color):
            items = [txt(title, 12, True, color)]
            for n, a in rows:
                items.append(ft.Container(
                    content=ft.Row([txt(n, 11, expand=True), txt(fmt(a), 11, True)]),
                    padding=pad_sym(8, 3), bgcolor=T()['bg'], border_radius=6))
            return card(ft.Column(items, spacing=4), padding=10)

        def loan_sec():
            rows = []
            for i in loan_insts:
                st_val = i.get('status') or 'pending'
                icon, col = {
                    'paid':       ('✅', T()['success']),
                    'calculated': ('🧮', T()['info']),
                    'pending':    ('⏳', T()['muted']),
                    'skipped':    ('⏭', T()['warning']),
                }.get(st_val, ('•', T()['muted']))
                rows.append(ft.Container(
                    content=ft.Row([
                        txt(f"{icon} قسط {i['installment_no']}", 11, True),
                        txt(f"{fmt(i['amount'])} ریال", 11, True, expand=True),
                        txt(f"سررسید {i['due_year']}/{i['due_month']:02d}",
                            9, color=T()['muted']),
                    ], spacing=6),
                    padding=pad_sym(8, 4), bgcolor=T()['bg'], border_radius=6))
            return card(ft.Column([txt("📋 اقساط وام این فیش", 12, True)] + rows,
                                  spacing=4), padding=10)

        def pdf1(ev):
            if not e: return
            try:
                # 🆕 اقساط وام را به دیکشنری فیش پیوست می‌کنیم
                pay_copy = dict(p)
                pay_copy['loan_insts'] = loan_insts
                path = build_pdf(os.path.join(export_dir(),
                    f"payslip_{p['emp_id']}_{p['year']}_{p['month']:02d}_{datetime.now():%Y%m%d_%H%M%S}.pdf"),
                    c, [dict(pay=pay_copy, emp=e, dept=dept, details=dets)])
                self.file_dialog(path, "📄 PDF ساخته شد", 1)
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا", str(ex))

        def col(label, val):
            return ft.Column([txt(label, 9, color=T()['muted']), txt(val, 11, True)],
                             spacing=1, expand=True)

        head = card(ft.Column([
            ft.Row([txt(f"{e.get('first_name','')} {e.get('last_name','')}" if e else '-',
                        14, True, expand=True),
                    badge(f"{(dept or {}).get('title','-')}",
                          alpha(T()['primary'], 0x22), T()['primary'], 9)]),
            ft.Row([col('دوره', f"{MONTHS[p['month']-1]} {p['year']}"),
                    col('روز', f"{p['work_days']:g}"), col('کد', str(p['emp_id']))]),
        ], spacing=6), padding=12)

        total = ft.Container(
            content=ft.Column([
                ft.Row([txt('جمع ناخالص', 12, color=T()['muted'], expand=True),
                        txt(fmt(p['gross_salary']), 13, True)]),
                ft.Row([txt('جمع کسورات', 12, color=T()['muted'], expand=True),
                        txt(fmt(p['gross_salary'] - p['net_salary']), 13, True, T()['danger'])]),
                ft.Divider(height=1),
                ft.Row([txt('خالص پرداختی', 13, True, expand=True),
                        txt(fmt(p['net_salary']), 15, True, T()['success'])]),
            ], spacing=6),
            padding=12, bgcolor=alpha(T()['accent'], 0x22), border_radius=12,
            border=border_all(2, T()['accent']))

        parts = [head,
                 sec('حقوق و مزایا',
                     [('حقوق پایه', p['base_salary_monthly'])]
                     + [(d['name'], d['amount']) for d in ben],
                     T()['primary'])]
        if extras: parts.append(sec('اضافات', extras, T()['primary']))
        if ded: parts.append(sec('کسورات',
                                 [(d['name'], d['amount']) for d in ded],
                                 T()['danger']))
        if loan_insts: parts.append(loan_sec())
        parts.append(total)
        def snap(ev):
            try:
                path = _png_path(f"payslip_{p['emp_id']}_{p['year']}_{p['month']:02d}")
                slip_png(path, c, p, e, dept, dets, loan_insts)
                self.file_dialog(path, "📸 اسکرین‌شات کامل فیش حقوقی")
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا در ساخت تصویر", str(ex))
        parts.append(ft.Row([gbtn('📄 PDF', _ic('PICTURE_AS_PDF'), pdf1, T()['primary'], expand=True),
                             gbtn('📸 اسکرین‌شات', _ic('PHOTO_CAMERA'), snap, T()['info'], expand=True)],
                            spacing=6))
        return ft.ListView(parts, spacing=8, expand=True, padding=pad_only(bottom=20))

    # ── قرارداد ──
    def contract_view(self, emp):
        c = self.db.q1("SELECT * FROM companies WHERE id=?", (self.cid,))
        depts = {d['id']: d for d in self.db.q("SELECT * FROM departments WHERE company_id=?", (self.cid,))}
        dept = depts.get(emp.get('dept_id'))
        template = (c.get('contract_template') or DEFAULT_CONTRACT)
        vars_map = {
            'company_name': c.get('name', ''), 'company_address': c.get('address', ''),
            'company_phone': c.get('phone', ''), 'company_manager': c.get('sign_manager', ''),
            'company_economic': c.get('economic_code', ''), 'company_reg': c.get('reg_no', ''),
            'first_name': emp.get('first_name', ''), 'last_name': emp.get('last_name', ''),
            'father_name': emp.get('father_name', ''), 'national_code': emp.get('national_code', ''),
            'id_number': emp.get('id_number', ''), 'id_issue_place': emp.get('id_issue_place', ''),
            'birth_date': emp.get('birth_date', ''), 'birth_place': emp.get('birth_place', ''),
            'address': emp.get('address', ''), 'mobile': emp.get('mobile', ''),
            'phone': emp.get('phone', ''), 'job_title': emp.get('job_title', ''),
            'dept_title': (dept or {}).get('title', ''),
            'employment_date': emp.get('employment_date', ''),
            'contract_end': emp.get('contract_end', ''),
            'daily_salary': fmt(emp.get('daily_salary', 0)),
            'monthly_salary': fmt((emp.get('daily_salary') or 0) * 30),
            'insurance_number': emp.get('insurance_number', ''),
            'work_start': c.get('default_work_start', '08:00'),
            'work_end': c.get('default_work_end', '16:00'),
            'today': jalali_today_str(),
        }
        preview = template
        for k, v in vars_map.items(): preview = preview.replace("{{" + k + "}}", str(v))
        editor = tf("متن قرارداد", preview, multiline=True, size=11)
        try: editor.min_lines = 12; editor.max_lines = 25
        except Exception: pass

        def save_template(ev):
            self.db.update('companies', self.cid, {'contract_template': editor.value or DEFAULT_CONTRACT})
            self.toast("✅ قالب ذخیره شد")

        def reset_default(ev):
            editor.value = DEFAULT_CONTRACT
            try: editor.update()
            except Exception: pass

        def print_pdf(ev):
            try:
                path = os.path.join(export_dir(),
                    f"contract_{emp['id']}_{datetime.now():%Y%m%d_%H%M%S}.pdf")
                build_contract_pdf(path, c, emp, editor.value or template,
                                   (dept or {}).get('title', ''))
                self.file_dialog(path, "📄 قرارداد PDF ساخته شد")
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا", str(ex))

        dlg = ft.AlertDialog(
            title=ft.Text(f"📄 قرارداد — {emp.get('first_name','')} {emp.get('last_name','')}", size=13),
            content=ft.Container(ft.Column([
                txt("متغیرهای قابل استفاده:", 11, True),
                txt("{{first_name}}, {{last_name}}, {{national_code}}, {{father_name}}, "
                    "{{address}}, {{mobile}}, {{job_title}}, {{dept_title}}, {{employment_date}}, "
                    "{{contract_end}}, {{daily_salary}}, {{monthly_salary}}, {{insurance_number}}, "
                    "{{company_name}}, {{company_address}}, {{company_phone}}, {{company_manager}}, "
                    "{{work_start}}, {{work_end}}, {{today}}", 9, color=T()['muted']),
                editor,
            ], scroll=ft.ScrollMode.AUTO, spacing=6, tight=True),
                width=min((self.page.width or 400) - 40, 460),
                height=min((self.page.height or 700) * 0.7, 560)),
            actions=[tbtn("پیش‌فرض", reset_default), tbtn("💾 ذخیره قالب", save_template),
                     gbtn("📄 PDF", _ic("PICTURE_AS_PDF"), print_pdf, T()['success']),
                     tbtn("بستن", lambda e: self.close_dlg(dlg))])
        self.open_dlg(dlg)

    # ── بیشتر ──
    def v_more(self):
        def tile(icon, title, sub, fn):
            return card(ft.Row([
                ft.Container(ft.Icon(icon, color=T()['primary'], size=18),
                             bgcolor=T()['accent'], width=38, height=38,
                             border_radius=19, alignment=center()),
                ft.Column([txt(title, 12, True), txt(sub, 10, color=T()['muted'])],
                          spacing=0, expand=True),
                ft.Icon(_ic("CHEVRON_LEFT"), color=T()['muted'], size=16),
            ], vertical_alignment=ft.CrossAxisAlignment.CENTER, spacing=10),
                padding=10, on_click=fn)
        items = [
            tile(_ic("CARD_GIFTCARD"), "مزایا و استثناها", "تعریف مزایا و استثنا",
                 lambda e: self.push("مزایا", self.v_benefits)),
            tile(_ic("ACCOUNT_BALANCE_WALLET"), "وام و پاداش و کسورات",
                 "مدیریت وام، پاداش و کسورات", lambda e: self.push("وام و پاداش", self.v_loans)),
            tile(_ic("CELEBRATION"), "عیدی و سنوات", "محاسبه سالانه",
                 lambda e: self.push("عیدی و سنوات", self.v_eid)),
            tile(_ic("ASSESSMENT"), "گزارشات", "خلاصه و CSV و سند",
                 lambda e: self.push("گزارشات", self.v_reports)),
            tile(_ic("SETTINGS"), "تنظیمات", "نرخ‌ها و قوانین",
                 lambda e: self.push("تنظیمات", self.v_settings)),
            tile(_ic("BUSINESS"), "اطلاعات و لوگوی شرکت", "نام، آدرس، امضا، لوگو",
                 lambda e: self.company_form()),
            tile(_ic("BACKUP"), "پشتیبان‌گیری", "ذخیره/بازگردانی",
                 lambda e: self.push("پشتیبان", self.v_backup)),
            tile(_ic("DESCRIPTION"), "مدیریت قالب قرارداد", "ویرایش قالب پیش‌فرض با متغیرهای فارسی",
                 lambda e: self.push("قالب قرارداد", self.v_contract_manager)),
            tile(_ic("WIFI"), "اشتراک نسخه وب", "اجرای لوکال‌هاست برای دیگران در شبکه",
                 lambda e: self.push("اشتراک نسخه وب", self.v_webshare)),
            tile(_ic("LOCK"), "تغییر رمز", "رمز ورود", lambda e: self.password_form()),
            tile(_ic("PALETTE"), "تغییر تم", "نیلی، زمرد، غروب", self.theme_picker),
            tile(_ic("DARK_MODE", "BRIGHTNESS_6"), "حالت تاریک", "روز/شب", self.toggle_theme),
            tile(_ic("LOGOUT"), "خروج", "صفحه ورود", lambda e: self.show_login()),
        ]
        items.append(card(ft.Column([
            txt("عرفان حساب | سیستم جامع حقوق و دستمزد", 13, True, T()['primary']),
            txt(f'توسعه‌دهنده: {DEVELOPER}', 11, True),
            txt(f'پشتیبانی: {DEVELOPER_PHONE}', 11, color=T()['muted']),
        ], spacing=2), padding=12))
        return ft.ListView(items, spacing=6, expand=True, padding=pad_only(bottom=20))

    def company_form(self):
        c = self.db.q1("SELECT * FROM companies WHERE id=?", (self.cid,))
        spec = [dict(key='name', label='نام شرکت', required=True),
                dict(key='reg_no', label='شناسه ملی'),
                dict(key='economic_code', label='کد اقتصادی', kb=True),
                dict(key='address', label='آدرس', type='multiline'),
                dict(key='phone', label='تلفن', kb=True),
                dict(key='email', label='ایمیل'),
                dict(key='website', label='وب‌سایت'),
                dict(key='postal_code', label='کد پستی', kb=True),
                dict(key='sign_manager', label='مدیرعامل'),
                dict(key='sign_accountant', label='حسابدار'),
                dict(key='insurance_rate', label='بیمه کارگر %', type='float'),
                dict(key='employer_insurance_rate', label='بیمه کارفرما %', type='float'),
                dict(key='unemployment_rate', label='بیمه بیکاری %', type='float'),
                dict(key='default_work_start', label='ساعت شروع کار'),
                dict(key='default_work_end', label='ساعت پایان کار')]

        def save(v):
            if not (0 <= v['insurance_rate'] <= 100 and 0 <= v['employer_insurance_rate'] <= 100
                    and 0 <= v['unemployment_rate'] <= 100):
                return "درصد بیمه باید بین ۰ تا ۱۰۰ باشد"
            self.db.update('companies', self.cid, v)
            self.toast("✅ ذخیره شد"); return None
        self.form("🏢 اطلاعات شرکت", spec, c, save)

    def _pick_logo(self):
        try:
            fp = K(ft.FilePicker, on_result=self._on_logo_picked)
            self.page.overlay.append(fp); self.page.update()
            try: fp.pick_files(allow_multiple=False, allowed_extensions=["jpg","jpeg","png","webp"], with_data=True)
            except Exception:
                try: fp.pick_files()
                except Exception: pass
        except Exception:
            log_error(traceback.format_exc())
            self.toast("انتخاب فایل پشتیبانی نمی‌شود", True)

    def _on_logo_picked(self, e):
        try:
            files = getattr(e, 'files', None) or []
            if not files:
                p = getattr(e, 'path', None)
                if p: files = [type('F', (), {'path': p})()]
            if not files: return
            path = getattr(files[0], 'path', None)
            if not path or not os.path.isfile(path): return
            with open(path, 'rb') as fh: data = fh.read()
            if Image is not None:
                try:
                    img = Image.open(io.BytesIO(data))
                    img.thumbnail((300, 300))
                    buf = io.BytesIO()
                    img.convert('RGB').save(buf, format='PNG')
                    data = buf.getvalue()
                except Exception: pass
            b64 = base64.b64encode(data).decode('ascii')
            self.db.update('companies', self.cid, {'logo': b64})
            self.toast("✅ لوگو ذخیره شد"); self.refresh()
        except Exception:
            log_error(traceback.format_exc()); self.toast("خطا در ذخیره لوگو", True)

    def password_form(self):
        spec = [dict(key='old', label='رمز فعلی', type='password'),
                dict(key='new', label='رمز جدید', type='password'),
                dict(key='confirm', label='تکرار رمز', type='password')]
        def save(v):
            row = self.db.q1("SELECT admin_password FROM companies WHERE id=?", (self.cid,))
            if not check_pw(v['old'], row['admin_password']): return "رمز فعلی اشتباه است"
            if len(v['new']) < 8: return "رمز جدید باید حداقل ۸ کاراکتر باشد"
            if v['new'] != v['confirm']: return "رمز و تکرار یکی نیست"
            self.db.x("UPDATE companies SET admin_password=? WHERE id=?", (hash_pw(v['new']), self.cid))
            self.toast("✅ رمز تغییر کرد"); return None
        self.form("🔒 تغییر رمز", spec, {}, save)

    # ── مزایا و استثنا (اصلاح‌شده) ──
    def v_benefits(self):
        c = self.db.company_data(self.cid)
        ben = [b for b in c['benefits'] if b['year'] == self.year]
        emps = {e['id']: e for e in c['employees']}
        depts = {d['id']: d for d in c['departments']}

        def exception_list(b):
            return [ex for ex in c['benefit_exceptions'] if ex['benefit_id'] == b['id']]

        def bform(b):
            spec = [dict(key='title', label='عنوان', required=True),
                    dict(key='amount', label='مبلغ ماهانه', type='money'),
                    dict(key='taxable', label='مشمول مالیات', type='bool'),
                    dict(key='insurable', label='مشمول بیمه', type='bool'),
                    dict(key='severance_basis', label='جزو مزد ثابت برای مبنای عیدی و سنوات (فقط مزایای مستمرِ شغلی)', type='bool'),
                    dict(key='calc_type', label='نوع محاسبه', type='dropdown',
                         options=[('fixed','مبلغ ثابت'), ('child','بر اساس فرزند'),
                                  ('marital','فقط متاهل‌ها'), ('percent','درصدی')])]
            def save(v):
                v['year'] = self.year
                try:
                    if b:
                        self.db.update('benefits', b['id'], v)
                        saved_id = b['id']
                    else:
                        saved_id = self.db.insert('benefits', dict(v, company_id=self.cid))
                    _sync_annual_rates(self.db, self.cid, 'benefits', v, saved_id)
                except Exception as ex:
                    log_error(traceback.format_exc())
                    return f'ذخیره مزایا انجام نشد: {ex}'
                return None
            def delete():
                self.db.delete('benefits', b['id']); self.refresh()
            self.form("✏️ ویرایش" if b else f"➕ مزایای {self.year}", spec,
                      b or dict(taxable=1, insurable=1, severance_basis=0, calc_type='fixed'), save,
                      delete if b else None)

        def exceptions_form(b):
            """فرم مدیریت استثناها (اصلاح‌شده)."""
            # نمایش لیست از DB هر بار
            exs_holder = ft.Column(spacing=4)
            emp_opts = [(0, '— هیچ‌کدام —')] + [(e['id'], f"{e['first_name']} {e['last_name']}")
                                                 for e in c['employees']]
            dept_opts = [(0, '— هیچ‌کدام —')] + [(d['id'], d['title']) for d in c['departments']]

            def reload_exceptions():
                return self.db.q("SELECT * FROM benefit_exceptions WHERE benefit_id=?", (b['id'],))

            def rebuild():
                exs_holder.controls.clear()
                current = reload_exceptions()
                for ex in current:
                    emp = emps.get(ex.get('emp_id'))
                    dept = depts.get(ex.get('dept_id'))
                    if emp: who = f"👤 {emp.get('first_name','')} {emp.get('last_name','')}"
                    elif dept: who = f"🏢 {dept.get('title','')}"
                    else: who = '؟'
                    def make_del(eid):
                        def h(ev):
                            self.db.delete('benefit_exceptions', eid)
                            self.toast("حذف شد"); rebuild()
                        return h
                    exs_holder.controls.append(card(ft.Row([
                        txt(who, 11, True, expand=True),
                        txt(ex.get('reason') or '', 10, color=T()['muted']),
                        iconbtn(_ic("DELETE"), make_del(ex['id']), '#c0392b', 18),
                    ]), padding=6))
                if not current:
                    exs_holder.controls.append(txt("استثنایی ثبت نشده", 10, color=T()['muted']))
                try: exs_holder.update()
                except Exception: pass

            emp_sel = dd('انتخاب پرسنل', emp_opts, 0, expand=True)
            dept_sel = dd('انتخاب دپارتمان', dept_opts, 0, expand=True)
            reason = tf('دلیل (اختیاری)')

            def add_exc(ev):
                # ✅ استفاده از تابع ایمن برای تبدیل
                emp_id = to_int_or_none(emp_sel.value)
                dept_id = to_int_or_none(dept_sel.value)
                if not emp_id and not dept_id:
                    self.toast("پرسنل یا دپارتمان را انتخاب کنید", True); return
                try:
                    self.db.insert('benefit_exceptions', dict(
                        benefit_id=b['id'], company_id=self.cid,
                        emp_id=emp_id, dept_id=dept_id,
                        reason=reason.value or ''))
                    emp_sel.value = '0'; dept_sel.value = '0'; reason.value = ''
                    self.toast("✅ استثنا اضافه شد"); rebuild()
                except Exception as ex:
                    log_error(traceback.format_exc())
                    self.toast(f"خطا: {ex}", True)

            rebuild()
            dlg = ft.AlertDialog(
                title=ft.Text(f"🚫 استثنا برای «{b['title']}»", size=13),
                content=ft.Container(ft.Column([
                    txt("پرسنل یا دپارتمان‌هایی که این مزایا به آن‌ها تعلق نمی‌گیرد:",
                        11, color=T()['muted']),
                    ft.Container(exs_holder, height=200, padding=6, bgcolor=T()['bg'],
                                 border_radius=8),
                    ft.Divider(height=1),
                    txt("➕ افزودن استثنای جدید", 11, True),
                    emp_sel, dept_sel, reason,
                    wide(lambda: gbtn("افزودن", _ic("ADD"), add_exc, T()['primary'], expand=True)),
                ], scroll=ft.ScrollMode.AUTO, spacing=6, tight=True),
                    width=min((self.page.width or 400) - 40, 440),
                    height=min((self.page.height or 700) * 0.75, 600)),
                actions=[tbtn("بستن", lambda e: self.close_dlg(dlg))])
            self.open_dlg(dlg)

        items = []
        for b in ben:
            exc_count = len(exception_list(b))
            items.append(card(ft.Column([
                ft.Row([
                    ft.Column([txt(b['title'], 13, True),
                               txt(f"{fmt(b['amount'])} ریال", 11, color=T()['muted'])],
                              spacing=2, expand=True),
                    ft.Column([
                        iconbtn(_ic("EDIT"), lambda ev, bb=b: bform(bb), T()['accent'], 18),
                        iconbtn(_ic("BLOCK"), lambda ev, bb=b: exceptions_form(bb), '#c0392b', 18),
                    ], spacing=0),
                ]),
                ft.Row([
                    badge("مالیات" if b['taxable'] else "معاف",
                          T()['warning'] if b['taxable'] else T()['success'], '#ffffff', 8),
                    badge("بیمه" if b['insurable'] else "غیر بیمه",
                          T()['info'] if b['insurable'] else T()['muted'], '#ffffff', 8),
                    badge(f"🚫 {exc_count} استثنا" if exc_count else "بدون استثنا",
                          T()['danger'] if exc_count else T()['muted'], '#ffffff', 8),
                ], spacing=4, wrap=True),
            ], spacing=4), padding=10))
        self.set_fab(_ic("ADD"), lambda e: bform(None))
        hint = ("💡 «حق تاهل» فقط برای متاهل‌ها، «حق اولاد» بر اساس تعداد فرزند. "
                "با دکمه 🚫 می‌توانید پرسنل یا دپارتمان‌های مستثنا را تعیین کنید.")
        return ft.Column([
            self.period_bar(self.refresh, False),
            txt(hint, 9, color=T()['muted']),
            ft.ListView(items or [self.empty(f"مزایایی برای {self.year} ثبت نشده")],
                        expand=True, spacing=6, padding=pad_only(bottom=90))
        ], expand=True, spacing=6)

    # ── وام، پاداش، کسورات ──
    def v_loans(self):
        c = self.db.company_data(self.cid)
        emps = {e['id']: e for e in c['employees']}
        opts = [(e['id'], f"{e['first_name']} {e['last_name']}")
                for e in c['employees'] if e['is_active']]
        st = {'tab': 0, 'q': '', 'filter': 'all'}

        # ═══════════════════════════════════════════
        #  فرم‌ها
        # ═══════════════════════════════════════════
        def loan_form(existing=None):
            spec = [dict(key='emp_id', label='پرسنل', type='dropdown',
                         options=opts, cast=int, required=True),
                    dict(key='principal', label='مبلغ وام (ریال)', type='money', required=True),
                    dict(key='count', label='تعداد اقساط', type='int', required=True),
                    dict(key='sy', label='سال شروع', type='int'),
                    dict(key='sm', label='ماه شروع', type='int'),
                    dict(key='purpose', label='هدف وام')]
            def save(v):
                if not (1300 <= v['sy'] <= 1500): return "سال شروع معتبر نیست"
                if not 1 <= v['sm'] <= 12: return "ماه شروع باید ۱ تا ۱۲ باشد"
                if v['count'] <= 0 or v['count'] > 120: return "تعداد اقساط باید ۱ تا ۱۲۰ باشد"
                if v['principal'] <= 0: return "مبلغ وام معتبر نیست"
                if not existing:
                    self.db.save_loan(self.cid, v['emp_id'], v['principal'],
                                      v['count'], v['sy'], v['sm'], v.get('purpose', ''))
                else:
                    paid_count = self.db.q1(
                        "SELECT COUNT(*) AS n FROM loan_installments "
                        "WHERE loan_id=? AND status='paid'",
                        (existing['id'],))['n']
                    schedule_changed = (int(v['principal']) != int(existing['principal']) or
                                        int(v['count']) != int(existing['install_count']) or
                                        int(v['sy']) != int(existing['start_year']) or
                                        int(v['sm']) != int(existing['start_month']) or
                                        int(v['emp_id']) != int(existing['emp_id']))
                    if paid_count and schedule_changed:
                        return 'اقساط پرداخت‌شده وجود دارد؛ فقط «هدف وام» قابل ویرایش است.'
                    if paid_count:
                        self.db.update('loans', existing['id'],
                                       {'purpose': v.get('purpose', '')})
                    else:
                        principal = int(v['principal']); count = int(v['count'])
                        each = principal // count
                        with self.db.tx() as conn:
                            conn.execute("""UPDATE loans SET emp_id=?,principal=?,
                                install_count=?,each_amount=?,start_year=?,start_month=?,
                                remaining_balance=?,purpose=?,status=0 WHERE id=?""",
                                (v['emp_id'], principal, count, each, v['sy'], v['sm'],
                                 principal, v.get('purpose', ''), existing['id']))
                            conn.execute('DELETE FROM loan_installments WHERE loan_id=?',
                                         (existing['id'],))
                            for i in range(count):
                                dy = int(v['sy']) + ((int(v['sm']) + i - 1) // 12)
                                dm = ((int(v['sm']) + i - 1) % 12) + 1
                                amt = each if i < count - 1 else principal - each * (count - 1)
                                conn.execute("""INSERT INTO loan_installments
                                    (loan_id,installment_no,due_year,due_month,amount,
                                     is_paid,status,original_due_year,original_due_month,defer_count)
                                    VALUES (?,?,?,?,?,0,'pending',?,?,0)""",
                                    (existing['id'], i + 1, dy, dm, amt, dy, dm))
                self.toast('✅ وام ذخیره شد'); return None
            initial = (dict(emp_id=existing['emp_id'], principal=existing['principal'],
                            count=existing['install_count'], sy=existing['start_year'],
                            sm=existing['start_month'], purpose=existing.get('purpose', ''))
                       if existing else dict(sy=self.year, sm=self.month))
            self.form('✏️ ویرایش وام' if existing else '💰 وام جدید', spec, initial, save)

        def bonus_form(existing=None):
            spec = [dict(key='emp_id', label='پرسنل', type='dropdown',
                         options=opts, cast=int, required=True),
                    dict(key='year', label='سال', type='int'),
                    dict(key='month', label='ماه', type='int'),
                    dict(key='amount', label='مبلغ پاداش (ریال)', type='money', required=True),
                    dict(key='reason', label='دلیل پاداش'),
                    dict(key='taxable', label='مشمول مالیات', type='bool'),
                    dict(key='insurable', label='مشمول بیمه', type='bool')]
            def save(v):
                if not 1 <= v['month'] <= 12: return "ماه معتبر نیست"
                if not 1300 <= v['year'] <= 1500: return "سال معتبر نیست"
                if existing:
                    self.db.update('bonuses', existing['id'], v)
                else:
                    self.db.insert('bonuses', dict(v, company_id=self.cid,
                                                   payment_status='pending'))
                self.toast("✅ پاداش ذخیره شد"); return None
            self.form("✏️ ویرایش پاداش" if existing else "🎁 پاداش جدید", spec,
                      existing or dict(year=self.year, month=self.month,
                                       taxable=1, insurable=1), save,
                      (lambda: self.confirm('حذف شود؟',
                          lambda: (self.db.delete('bonuses', existing['id']), self.refresh()),
                          'حذف پاداش')) if existing else None)

        def deduction_form(existing=None):
            spec = [dict(key='emp_id', label='پرسنل', type='dropdown',
                         options=opts, cast=int, required=True),
                    dict(key='year', label='سال', type='int'),
                    dict(key='month', label='ماه', type='int'),
                    dict(key='amount', label='مبلغ کسورات (ریال)', type='money', required=True),
                    dict(key='reason', label='دلیل کسورات')]
            def save(v):
                if not 1 <= v['month'] <= 12: return "ماه معتبر نیست"
                if not 1300 <= v['year'] <= 1500: return "سال معتبر نیست"
                if existing:
                    self.db.update('deductions', existing['id'], v)
                else:
                    self.db.insert('deductions', dict(v, company_id=self.cid,
                                                     payment_status='pending'))
                self.toast("✅ کسورات ذخیره شد"); return None
            self.form("✏️ ویرایش کسورات" if existing else "➖ کسورات جدید", spec,
                      existing or dict(year=self.year, month=self.month), save,
                      (lambda: self.confirm('حذف شود؟',
                          lambda: (self.db.delete('deductions', existing['id']), self.refresh()),
                          'حذف کسورات')) if existing else None)

        # ═══════════════════════════════════════════
        #  دیالوگ مدیریت یک قسط
        # ═══════════════════════════════════════════
        def installment_actions(inst, emp, loan):
            if inst.get('status') == 'paid':
                self.info('قسط پرداخت‌شده',
                          'این قسط در فیش پرداخت‌شده کسر شده و قابل تغییر نیست.')
                return

            year_f = tf('سال مقصد', inst['due_year'], kb=True, width=100)
            month_f = dd('ماه مقصد', [(i + 1, m) for i, m in enumerate(MONTHS)],
                         inst['due_month'], width=140)
            reason_f = tf('دلیل', inst.get('skip_reason') or '', expand=True)

            def do_defer(ev):
                ny = parse_int(year_f.value); nm = int(month_f.value or 1)
                if not (1300 <= ny <= 1500):
                    self.toast('سال معتبر نیست', True); return
                if ny == inst['due_year'] and nm == inst['due_month']:
                    self.toast('مقصد یکسان است', True); return
                with self.db.tx() as conn:
                    conn.execute("""UPDATE loan_installments
                        SET due_year=?, due_month=?, status='pending',
                            defer_count=COALESCE(defer_count,0)+1,
                            skip_reason=?,
                            original_due_year=COALESCE(original_due_year, due_year),
                            original_due_month=COALESCE(original_due_month, due_month)
                        WHERE id=?""",
                        (ny, nm, reason_f.value or 'تعویق', inst['id']))
                self.close_dlg(dlg)
                self.toast(f'✅ قسط به {MONTHS[nm-1]} {ny} منتقل شد')
                self.refresh()

            def do_skip(ev):
                with self.db.tx() as conn:
                    conn.execute("""UPDATE loan_installments
                        SET status='skipped', skip_reason=? WHERE id=?""",
                        (reason_f.value or 'رد ماه جاری', inst['id']))
                self.close_dlg(dlg); self.toast('⏭ قسط این ماه رد شد'); self.refresh()

            def do_unskip(ev):
                with self.db.tx() as conn:
                    conn.execute("""UPDATE loan_installments
                        SET status='pending', skip_reason=NULL WHERE id=?""", (inst['id'],))
                self.close_dlg(dlg); self.toast('✅ قسط به حالت عادی برگشت'); self.refresh()

            def do_delete(ev):
                self.close_dlg(dlg)
                self.confirm('این قسط حذف شود؟',
                             lambda: (self.db.delete('loan_installments', inst['id']),
                                      self.refresh()), 'حذف قسط')

            status_fa = {'pending': '⏳ در انتظار',
                         'calculated': '🧮 در فیش محاسبه‌شده',
                         'paid': '✅ پرداخت‌شده',
                         'deferred': '📅 تعویق‌خورده',
                         'skipped': '⏭ رد‌شده',
                         'waived': '🎁 بخشیده‌شده'}.get(inst.get('status') or 'pending')

            actions = [tbtn('بستن', lambda e: self.close_dlg(dlg))]
            if inst.get('status') == 'skipped':
                actions.insert(0, gbtn('↩️ فعال‌سازی مجدد', _ic('UNDO'),
                                       do_unskip, T()['success']))
            else:
                actions.insert(0, gbtn('⏭ رد این ماه', _ic('SKIP_NEXT'),
                                       do_skip, T()['warning']))
            actions.insert(0, gbtn('📅 تعویق', _ic('EDIT_CALENDAR'),
                                   do_defer, T()['primary']))
            actions.insert(0, tbtn('🗑 حذف', do_delete, '#c0392b'))

            dlg = ft.AlertDialog(
                title=ft.Text(f"قسط {inst['installment_no']} از {loan['install_count']}", size=13),
                content=ft.Container(ft.Column([
                    ft.Row([
                        badge(f"مبلغ {fmt(inst['amount'])}", T()['accent'], T()['primary'], 10),
                        badge(status_fa,
                              T()['success'] if inst.get('status') == 'paid' else T()['primary'],
                              '#ffffff', 10),
                    ], spacing=6),
                    ft.Divider(height=1),
                    txt(f"پرسنل: {emp.get('first_name','')} {emp.get('last_name','')}", 11),
                    txt(f"سررسید فعلی: {inst['due_year']}/{inst['due_month']:02d}", 11),
                    txt(f"سررسید اصلی: {inst.get('original_due_year') or inst['due_year']}/"
                        f"{(inst.get('original_due_month') or inst['due_month']):02d}",
                        10, color=T()['muted']),
                    txt(f"تعداد تعویق: {inst.get('defer_count') or 0} بار", 10,
                        color=T()['muted']),
                    ft.Divider(height=1),
                    txt("📅 انتقال به دوره دیگر:", 11, True),
                    ft.Row([year_f, month_f], spacing=6),
                    reason_f,
                ], scroll=ft.ScrollMode.AUTO, spacing=6, tight=True),
                    width=min((self.page.width or 400) - 40, 460),
                    height=min((self.page.height or 700) * 0.7, 520)),
                actions=actions)
            self.open_dlg(dlg)

        # ═══════════════════════════════════════════
        #  دیالوگ جزئیات وام
        # ═══════════════════════════════════════════
        def loan_detail(l, e):
            insts = self.db.q("""SELECT * FROM loan_installments
                WHERE loan_id=? ORDER BY due_year, due_month, installment_no""",
                (l['id'],))
            paid = sum(1 for i in insts if i.get('status') == 'paid')
            calc = sum(1 for i in insts if i.get('status') == 'calculated')
            pend = sum(1 for i in insts if (i.get('status') or 'pending') == 'pending')
            skip = sum(1 for i in insts if i.get('status') == 'skipped')

            def inst_chip(i):
                st_val = i.get('status') or 'pending'
                conf = {
                    'paid':       ('✅', T()['success'], '#ffffff'),
                    'calculated': ('🧮', T()['info'], '#ffffff'),
                    'pending':    ('⏳', T()['muted'], '#ffffff'),
                    'skipped':    ('⏭', T()['warning'], '#ffffff'),
                    'deferred':   ('📅', T()['purple'], '#ffffff'),
                    'waived':     ('🎁', T()['accent'], T()['primary']),
                }.get(st_val, ('•', T()['muted'], '#ffffff'))
                icon, bg, fg = conf
                return card(ft.Row([
                    ft.Container(txt(icon, 16), alignment=center(),
                                 width=30, height=30, bgcolor=bg, border_radius=15),
                    ft.Column([
                        txt(f"قسط {i['installment_no']} — {fmt(i['amount'])} ریال", 11, True),
                        txt(f"سررسید: {i['due_year']}/{i['due_month']:02d}"
                            + (f"  •  اصل: {i.get('original_due_year')}/"
                               f"{(i.get('original_due_month') or i['due_month']):02d}"
                               if (i.get('original_due_year') and
                                   (i['due_year'] != i.get('original_due_year') or
                                    i['due_month'] != i.get('original_due_month'))) else '')
                            + (f"  •  {i.get('skip_reason')}" if i.get('skip_reason') else ''),
                            9, color=T()['muted']),
                    ], spacing=1, expand=True),
                    ft.Icon(_ic('CHEVRON_LEFT'), color=T()['muted'], size=14),
                ], spacing=8), padding=6,
                    on_click=lambda ev, ii=i: (self.close_dlg(dlg),
                                               installment_actions(ii, e, l)))

            def delete_loan():
                self.db.delete('loans', l['id'])
                self.toast("وام حذف شد"); self.refresh()

            dlg = ft.AlertDialog(
                title=ft.Text(f"وام {e.get('first_name','')} {e.get('last_name','')}", size=13),
                content=ft.Container(ft.Column([
                    ft.Row([
                        badge(f"اصل {fmt(l['principal'])}", T()['primary'], '#ffffff', 9),
                        badge(f"مانده {fmt(l['remaining_balance'])}",
                              T()['danger'] if l['remaining_balance'] else T()['success'],
                              '#ffffff', 9),
                    ], spacing=6),
                    ft.Row([
                        badge(f"✅ {paid} پرداخت", T()['success'], '#ffffff', 8),
                        badge(f"🧮 {calc} محاسبه", T()['info'], '#ffffff', 8),
                        badge(f"⏳ {pend} در انتظار", T()['muted'], '#ffffff', 8),
                        badge(f"⏭ {skip} رد‌شده", T()['warning'], '#ffffff', 8),
                    ], spacing=4, wrap=True),
                    txt(f"هدف: {l.get('purpose') or '-'}", 10, color=T()['muted']),
                    ft.Divider(height=1),
                    txt("📋 لیست اقساط (برای مدیریت کلیک کنید)", 11, True),
                    ft.Column([inst_chip(i) for i in insts], spacing=4),
                ], scroll=ft.ScrollMode.AUTO, spacing=6, tight=True),
                    width=min((self.page.width or 400) - 40, 500),
                    height=min((self.page.height or 700) * 0.8, 620)),
                actions=[tbtn('✏️ ویرایش وام',
                              lambda ev: (self.close_dlg(dlg), loan_form(l))),
                         tbtn("🗑 حذف وام",
                              lambda ev: (self.close_dlg(dlg),
                                          self.confirm("وام و اقساط حذف شوند؟",
                                                       delete_loan, "حذف وام")), "#c0392b"),
                         tbtn("بستن", lambda ev: self.close_dlg(dlg))])
            self.open_dlg(dlg)

        # ═══════════════════════════════════════════
        #  فیلترها
        # ═══════════════════════════════════════════
        def match_emp(e):
            if not e: return False
            q = st['q'].strip().lower()
            if not q: return True
            hay = (f"{e.get('first_name','')} {e.get('last_name','')} "
                   f"{e.get('national_code','')} {e['id']}").lower()
            return q in hay

        def match_status(status):
            f = st['filter']
            if f == 'all': return True
            return (status or 'pending') == f

        def loan_matches(l):
            e = emps.get(l['emp_id'])
            if not match_emp(e): return False
            if st['filter'] == 'all': return True
            if st['filter'] == 'active':   return l.get('status') != 1
            if st['filter'] == 'settled':  return l.get('status') == 1
            return True

        def bonus_matches(b):
            return match_emp(emps.get(b['emp_id'])) and match_status(b.get('payment_status'))

        def deduction_matches(d):
            return match_emp(emps.get(d['emp_id'])) and match_status(d.get('payment_status'))

        # ═══════════════════════════════════════════
        #  رندر بخش‌ها
        # ═══════════════════════════════════════════
        def render_loans():
            items = []
            for l in c['loans']:
                e = emps.get(l['emp_id'])
                if not e or not loan_matches(l): continue
                insts = self.db.q(
                    "SELECT status, COUNT(*) as n FROM loan_installments "
                    "WHERE loan_id=? GROUP BY status",
                    (l['id'],))
                stat = {r['status'] or 'pending': r['n'] for r in insts}
                paid_n = stat.get('paid', 0)
                pend_n = stat.get('pending', 0)
                defer_n = stat.get('skipped', 0)
                total = l['install_count'] or 1
                pct = paid_n / total

                items.append(card(ft.Column([
                    ft.Row([
                        ft.Container(
                            content=txt(f"{e.get('first_name','')[:1]}{e.get('last_name','')[:1]}",
                                        13, True, '#ffffff'),
                            width=36, height=36, bgcolor=T()['primary'],
                            border_radius=18, alignment=center()),
                        ft.Column([
                            txt(f"{e.get('first_name','')} {e.get('last_name','')}",
                                12, True, expand=True),
                            txt(f"اصل: {fmt(l['principal'])} | مانده: {fmt(l['remaining_balance'])}",
                                10, color=T()['muted']),
                        ], spacing=1, expand=True),
                        badge("تسویه" if l['status'] == 1 else "جاری",
                              T()['success'] if l['status'] == 1 else T()['accent'],
                              '#ffffff' if l['status'] == 1 else T()['primary'], 9),
                    ], spacing=8),
                    ft.Container(
                        ft.ProgressBar(value=pct, height=5, color=T()['success'],
                                       bgcolor=alpha(T()['success'], 0x22)),
                        border_radius=3),
                    ft.Row([
                        badge(f"✅ {paid_n}/{total}", T()['success'], '#ffffff', 8),
                        badge(f"⏳ {pend_n}", T()['muted'], '#ffffff', 8),
                        badge(f"⏭ {defer_n}", T()['warning'], '#ffffff', 8) if defer_n else ft.Container(),
                        ft.Container(expand=True),
                        txt(f"{pct*100:.0f}%", 10, True, T()['primary']),
                    ], spacing=4),
                ], spacing=5), padding=10,
                    on_click=lambda ev, ll=l, ee=e: loan_detail(ll, ee)))
            if not items:
                items.append(self.empty("وامی یافت نشد", _ic('ACCOUNT_BALANCE')))
            return items

        def render_bonuses():
            items = []
            for b in c['bonuses']:
                e = emps.get(b['emp_id'])
                if not e or not bonus_matches(b): continue
                st_val = b.get('payment_status') or 'pending'
                paid = st_val in ('paid', 'calculated')

                def make_del(bid):
                    return lambda ev: self.confirm(
                        "حذف شود؟",
                        lambda: (self.db.delete('bonuses', bid), self.refresh()),
                        'حذف پاداش')

                items.append(card(ft.Row([
                    ft.Column([
                        txt(f"{e.get('first_name','')} {e.get('last_name','')}", 12, True),
                        txt(f"{fmt(b['amount'])} ریال — {b.get('reason') or ''}", 10,
                            color=T()['muted']),
                        txt(f"{MONTHS[b['month']-1]} {b['year']}", 9, color=T()['muted']),
                    ], spacing=2, expand=True),
                    ft.Column([
                        badge(
                            {'pending': '⏳ در انتظار', 'calculated': '🧮 در فیش',
                             'paid': '✅ پرداخت‌شده'}.get(st_val, st_val),
                            {'pending': T()['muted'], 'calculated': T()['info'],
                             'paid': T()['success']}.get(st_val, T()['muted']),
                            '#ffffff', 8),
                        ft.Row([
                            iconbtn(_ic('EDIT'), lambda ev, bb=b: bonus_form(bb),
                                    T()['primary'], 16, 'ویرایش'),
                            iconbtn(_ic("DELETE"), make_del(b['id']),
                                    "#c0392b", 16, 'حذف'),
                        ], spacing=0),
                    ], spacing=4, horizontal_alignment=ft.CrossAxisAlignment.END),
                ], spacing=8), padding=8))
            if not items:
                items.append(self.empty("پاداشی یافت نشد", _ic('CARD_GIFTCARD')))
            return items

        def render_deductions():
            items = []
            for d0 in c.get('deductions', []):
                e = emps.get(d0['emp_id'])
                if not e or not deduction_matches(d0): continue
                st_val = d0.get('payment_status') or 'pending'
                applied = st_val == 'applied'

                def make_del(did):
                    return lambda ev: self.confirm(
                        "حذف شود؟",
                        lambda: (self.db.delete('deductions', did), self.refresh()),
                        'حذف کسورات')

                items.append(card(ft.Row([
                    ft.Column([
                        txt(f"{e.get('first_name','')} {e.get('last_name','')}", 12, True),
                        txt(f"{fmt(d0['amount'])} ریال — {d0.get('reason') or ''}", 10,
                            color=T()['muted']),
                        txt(f"{MONTHS[d0['month']-1]} {d0['year']}", 9, color=T()['muted']),
                    ], spacing=2, expand=True),
                    ft.Column([
                        badge('✅ اعمال‌شده' if applied else '⏳ در انتظار',
                              T()['success'] if applied else T()['muted'],
                              '#ffffff', 8),
                        ft.Row([
                            iconbtn(_ic('EDIT'), lambda ev, dd0=d0: deduction_form(dd0),
                                    T()['primary'], 16, 'ویرایش'),
                            iconbtn(_ic("DELETE"), make_del(d0['id']),
                                    "#c0392b", 16, 'حذف'),
                        ], spacing=0),
                    ], spacing=4, horizontal_alignment=ft.CrossAxisAlignment.END),
                ], spacing=8), padding=8))
            if not items:
                items.append(self.empty("کسوراتی یافت نشد", _ic('REMOVE_CIRCLE')))
            return items

        # ═══════════════════════════════════════════
        #  چیدمان نهایی
        # ═══════════════════════════════════════════
        body_holder = ft.ListView(spacing=6, expand=True)

        filter_opts = {
            0: [('all', 'همه'), ('active', 'جاری'), ('settled', 'تسویه‌شده')],
            1: [('all', 'همه'), ('pending', '⏳ در انتظار'),
                ('calculated', '🧮 در فیش'), ('paid', '✅ پرداخت‌شده')],
            2: [('all', 'همه'), ('pending', '⏳ در انتظار'),
                ('applied', '✅ اعمال‌شده')],
        }

        def refresh_body():
            body_holder.controls.clear()
            t = st['tab']
            if t == 0:
                body_holder.controls.extend(render_loans())
            elif t == 1:
                body_holder.controls.extend(render_bonuses())
            else:
                body_holder.controls.extend(render_deductions())
            try: body_holder.update()
            except Exception: pass

        filter_row = ft.Row(spacing=6, wrap=True)

        def rebuild_filters():
            filter_row.controls.clear()
            for key, label in filter_opts[st['tab']]:
                active = st['filter'] == key
                filter_row.controls.append(ft.Container(
                    content=txt(label, 10, True,
                                '#ffffff' if active else T()['primary']),
                    padding=pad_sym(10, 5), border_radius=14, ink=True,
                    bgcolor=T()['primary'] if active else alpha(T()['accent'], 0x44),
                    on_click=lambda ev, k=key: (st.update({'filter': k}),
                                                rebuild_filters(), refresh_body())))
            try: filter_row.update()
            except Exception: pass

        tab_defs = [('💰 وام‌ها', 0), ('🎁 پاداش‌ها', 1), ('➖ کسورات', 2)]
        tab_row = ft.Row(spacing=6)

        def switch_tab(idx):
            st['tab'] = idx
            st['filter'] = 'all'
            rebuild_tabs()
            rebuild_filters()
            refresh_body()

        def rebuild_tabs():
            tab_row.controls.clear()
            for label, idx in tab_defs:
                active = st['tab'] == idx
                tab_row.controls.append(ft.Container(
                    content=txt(label, 12, True,
                                '#ffffff' if active else T()['primary']),
                    padding=pad_sym(14, 8), border_radius=12, ink=True, expand=True,
                    alignment=center(),
                    bgcolor=T()['primary'] if active else alpha(T()['accent'], 0x33),
                    on_click=lambda ev, i=idx: switch_tab(i)))
            try: tab_row.update()
            except Exception: pass

        rebuild_tabs()
        rebuild_filters()
        refresh_body()

        def fab_handler(e):
            if st['tab'] == 0: loan_form()
            elif st['tab'] == 1: bonus_form()
            else: deduction_form()

        self.set_fab(_ic('ADD'), fab_handler)

        return ft.Column([
            card(tab_row, padding=8),
            card(ft.Column([
                tf("🔍 جستجو...", on_change=lambda e: (
                    st.update({'q': e.control.value or ''}), refresh_body()),
                   prefix=_ic('SEARCH'), size=12),
                filter_row,
            ], spacing=6), padding=8),
            body_holder,
        ], expand=True, spacing=6)

    def v_eid(self):
        c = self.db.company_data(self.cid)
        emps = {e['id']: e for e in c['employees']}
        recs = [r for r in c['eid_records'] if r['year'] == self.year]

        def go(e):
            try:
                n = self.svc.calculate_eid(self.cid, self.year)
            except Exception as ex:
                log_error(traceback.format_exc())
                self.info('تنظیمات سالانه ناقص است', str(ex))
                return
            self.toast(f"✅ {n} نفر محاسبه شد"); self.refresh()

        def pdf_eid(e):
            if not recs:
                self.toast("داده‌ای نیست", True); return
            try:
                pdf, _ = _pdf_init((210, 297))
                W, M = 210, 8
                pdf.add_page()
                pdf.set_fill_color(30, 58, 95); pdf.rect(M, 8, W - 2*M, 12, 'F')
                pdf.set_xy(M, 10); pdf.set_font("F", size=13); pdf.set_text_color(240, 180, 41)
                pdf.cell(W - 2*M, 8, rtl(f"گزارش عیدی و سنوات — سال {self.year}"), border=0, align='C')
                y = 26

                # 🆕 چیدمان ستون‌ها از راست به چپ
                headers = ["#", "نام و فامیل", "کارکرد سال", "حقوق ماهانه", "عیدی", "سنوات"]
                col_w   = [12, 60, 25, 40, 30, 30]
                headers_rtl = list(reversed(headers))
                col_w_rtl   = list(reversed(col_w))

                pdf.set_fill_color(240, 180, 41); pdf.set_text_color(30, 58, 95); pdf.set_font("F", size=9)
                x = M
                for i, h in enumerate(headers_rtl):
                    pdf.set_xy(x, y); pdf.cell(col_w_rtl[i], 7, rtl(h), border=1, align='C', fill=True)
                    x += col_w_rtl[i]
                y += 7

                pdf.set_text_color(0, 0, 0); pdf.set_font("F", size=8)
                te = ts = 0
                for idx, r in enumerate(recs, 1):
                    emp = emps.get(r['emp_id'])
                    if not emp:
                        continue
                    if y > 275:
                        pdf.add_page(); y = 20
                    vals = [str(idx), f"{emp.get('first_name','')} {emp.get('last_name','')}",
                            f"{r['work_days']:g}", fmt(r.get('monthly_salary') or 0),
                            fmt(r['amount']), fmt(r['severance'])]
                    vals_rtl = list(reversed(vals))     # 🆕
                    x = M
                    for i, v in enumerate(vals_rtl):
                        pdf.set_xy(x, y); pdf.cell(col_w_rtl[i], 6, rtl(v), border=1, align='C')
                        x += col_w_rtl[i]
                    y += 6
                    te += r['amount']; ts += r['severance']

                pdf.set_fill_color(240, 180, 41); pdf.set_font("F", size=9)
                pdf.set_text_color(30, 58, 95); pdf.set_xy(M, y)
                pdf.cell(W - 2*M, 8, rtl(f"جمع: عیدی {fmt(te)} — سنوات {fmt(ts)}"),
                        border=1, align='C', fill=True)

                path = os.path.join(export_dir(), f"eid_severance_{self.year}.pdf")
                pdf.output(path)
                self.file_dialog(path, "📄 PDF عیدی و سنوات")
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا", str(ex))

        items = []
        for r in recs:
            e = emps.get(r['emp_id'])
            if not e:
                continue
            items.append(card(ft.Column([
                txt(f"{e.get('first_name','')} {e.get('last_name','')}", 12, True),
                ft.Row([badge(f"🎁 عیدی {fmt(r['amount'])}", T()['success'], '#ffffff', 9),
                        badge(f"📅 سنوات {fmt(r['severance'])}", T()['primary'], '#ffffff', 9)],
                    spacing=4, wrap=True),
                txt(f"کارکرد سال: {r['work_days']:g} روز • حقوق ماهانه: {fmt(r.get('monthly_salary') or 0)}",
                    10, color=T()['muted'])], spacing=3), padding=10))
        total_e = sum(r['amount'] for r in recs)
        total_s = sum(r['severance'] for r in recs)
        parts = [self.period_bar(self.refresh, False),
                ft.Row([gbtn("🎁 محاسبه", _ic("CALCULATE"), go, T()['success'], expand=True),
                        obtn("📄 PDF", _ic("PICTURE_AS_PDF"), pdf_eid, expand=True)], spacing=6)]
        if recs:
            parts.append(card(ft.Row([
                txt(f"جمع عیدی: {fmt(total_e)}", 11, True, expand=True),
                txt(f"جمع سنوات: {fmt(total_s)}", 11, True)]),
                padding=10, border_color=T()['accent']))
        parts.append(ft.ListView(items or [self.empty("هنوز محاسبه نشده")], expand=True,
                                spacing=6, padding=pad_only(bottom=20)))
        return ft.Column(parts, expand=True, spacing=6)

    def v_reports(self):
        pays = self.svc.payrolls(self.cid, self.year, self.month)
        c = self.db.company_data(self.cid)
        emps = {e['id']: e for e in c['employees']}
        depts = {d['id']: d['title'] for d in c['departments']}

        def export(fn):
            def h(e):
                if not pays: self.toast("برای این ماه فیشی نیست", True); return
                try:
                    path = fn(self.db, self.svc, self.cid, self.year, self.month)
                    self.file_dialog(path)
                except Exception as ex:
                    log_error(traceback.format_exc()); self.info("خطا", str(ex))
            return h

        def s(k): return sum(p.get(k, 0) or 0 for p in pays)
        totals = card(ft.Column([
            ft.Row([txt("تعداد فیش", 11, expand=True), txt(str(len(pays)), 12, True)]),
            ft.Row([txt("ناخالص", 11, expand=True), txt(fmt(s('gross_salary')), 12, True)]),
            ft.Row([txt("بیمه کارگر", 11, expand=True), txt(fmt(s('insurance_emp')), 12, True)]),
            ft.Row([txt("بیمه کارفرما", 11, expand=True), txt(fmt(s('insurance_er')), 12, True)]),
            ft.Row([txt("مالیات", 11, expand=True), txt(fmt(s('tax')), 12, True)]),
            ft.Row([txt("اقساط وام", 11, expand=True), txt(fmt(s('loan_install')), 12, True)]),
            ft.Row([txt("خالص", 12, True, expand=True), txt(fmt(s('net_salary')), 13, True, T()['success'])]),
        ], spacing=4), padding=12, border_color=T()['accent'])
        by_dept = {}
        for p in pays:
            e = emps.get(p['emp_id'])
            title = depts.get((e or {}).get('dept_id'), 'بدون واحد')
            agg = by_dept.setdefault(title, [0, 0, 0])
            agg[0] += 1; agg[1] += p['gross_salary']; agg[2] += p['net_salary']
        dept_rows = [ft.Row([txt(f"{t} ({v[0]})", 11, expand=True), txt(fmt(v[2]), 11, True)])
                     for t, v in sorted(by_dept.items())]
        dept_card = card(ft.Column([txt("خالص به تفکیک واحد", 12, True)] + dept_rows, spacing=4),
                         padding=12) if dept_rows else ft.Container()
        def snap(ev):
            if not pays:
                self.toast("برای این ماه فیشی نیست", True); return
            try:
                path = _png_path(f"report_{self.year}_{self.month:02d}")
                report_png(path, c, self.year, self.month, pays, by_dept)
                self.file_dialog(path, "📸 اسکرین‌شات گزارش")
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا در ساخت تصویر", str(ex))
        return ft.ListView([
            self.period_bar(self.refresh), totals, dept_card,
            wide(lambda: obtn("📸 اسکرین‌شات گزارش", _ic("PHOTO_CAMERA"), snap, expand=True)),
            wide(lambda: obtn("📊 CSV جامع حقوق", _ic("FILE_DOWNLOAD"),
                              export(export_full_csv), expand=True)),
        ], expand=True, spacing=6, padding=pad_only(bottom=20))

    def v_backup(self):
        listing = ft.Column(spacing=6)
        def refresh_list():
            listing.controls.clear()
            files = sorted(glob.glob(os.path.join(export_dir(), "backup_*.db")), reverse=True)
            for f in files[:15]:
                listing.controls.append(card(ft.Row([
                    txt(os.path.basename(f), 10, expand=True, selectable=True),
                    tbtn("بازگردانی", lambda e, ff=f: self.confirm(
                        "اطلاعات فعلی جایگزین می‌شود (نسخه‌ی فعلی نگه داشته می‌شود). ادامه؟",
                        lambda: do_restore(ff), "بازگردانی"), "#c0392b")]), padding=6))
            if not files:
                listing.controls.append(txt("هنوز پشتیبانی ساخته نشده", 10, color=T()['muted']))
        def do_restore(f):
            try:
                self.db.restore(f)
                self.cid = self.db.active_company()
                self.toast("✅ بازگردانی انجام شد"); self.go_root(0)
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا در بازگردانی", str(ex))
        def do(e):
            try:
                path = self.db.backup()
                self.file_dialog(path, "✅ پشتیبان ساخته شد")
                refresh_list(); self.page.update()
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا", str(ex))
        refresh_list()
        return ft.ListView([
            wide(lambda: gbtn("💾 ساخت پشتیبان", _ic("BACKUP"), do, T()['success'], expand=True)),
            txt(f"📁 {export_dir()}", 9, color=T()['muted'], selectable=True),
            txt("پشتیبان‌های موجود:", 12, True), listing,
        ], expand=True, spacing=8, padding=pad_only(bottom=20))

    def v_settings(self):
        def copy_year(e):
            src = self.db.previous_settings_year(self.cid, self.year)
            if not src:
                self.toast(f"سال قبل از {self.year} تنظیماتی ندارد", True); return
            def go():
                n = self.db.copy_year(self.cid, src, self.year)
                self.toast(f"✅ {n} مورد از سال {src} به {self.year} کپی شد" if n
                           else f"تنظیمات سال {self.year} از قبل وجود دارد", n == 0)
            self.confirm(f"تنظیمات سال {src} به {self.year} کپی شود؟", go, "کپی", False)
        def tile(icon, title, fn=None, action=None):
            return card(ft.Row([ft.Icon(icon, color=T()['accent'], size=18),
                                txt(title, 12, True, expand=True),
                                ft.Icon(_ic("CHEVRON_LEFT"), color=T()['muted'], size=16)]),
                        padding=10, on_click=action or (lambda e: self.push(title, fn)))
        return ft.ListView([
            self.period_bar(self.refresh, False),
            tile(_ic("PERCENT"), "نرخ‌های قانون کار", self.v_rates),
            tile(_ic("STAIRS"), "پله‌های مالیاتی", self.v_tax),
            tile(_ic("APARTMENT"), "دپارتمان‌ها", self.v_depts),
            tile(_ic("CONTENT_COPY"), "کپی تنظیمات از سال قبل", action=copy_year),
        ], spacing=6, expand=True)

    def crud(self, table, spec, rows, title_fn, sub_fn, add_title, defaults=None, validate=None):
        def form(r):
            def save(v):
                if validate:
                    try:
                        m = validate(v, r)
                    except TypeError:
                        m = validate(v)
                    if m: return m
                if r:
                    self.db.update(table, r['id'], v)
                    saved_id = r['id']
                else:
                    saved_id = self.db.insert(table, dict(v, company_id=self.cid))
                _sync_annual_rates(self.db, self.cid, table, v, saved_id)
                return None
            def delete():
                try: self.db.delete(table, r['id'])
                except sqlite3.IntegrityError as ex: self.toast(str(ex), True)
                self.refresh()
            self.form("✏️ ویرایش" if r else add_title, spec, r or (defaults or {}), save,
                      delete if r else None)
        items = [card(ft.Row([
            ft.Column([txt(title_fn(r), 12, True), txt(sub_fn(r), 10, color=T()['muted'])],
                      spacing=1, expand=True),
            ft.Icon(_ic("EDIT"), color=T()['accent'], size=18)]),
            padding=8, on_click=lambda e, rr=r: form(rr)) for r in rows]
        self.set_fab(_ic("ADD"), lambda e: form(None))
        return ft.ListView(items or [self.empty("موردی ثبت نشده")], spacing=6,
                           expand=True, padding=pad_only(bottom=90))

    def v_rates(self):
        rows = self.db.q("SELECT * FROM rate_years WHERE company_id=? ORDER BY year DESC", (self.cid,))
        spec = [dict(key='year', label='سال', type='int', required=True),
                dict(key='overtime_coeff', label='ضریب اضافه‌کاری', type='float'),
                dict(key='night_coeff', label='ضریب شب‌کاری', type='float'),
                dict(key='shift_percent', label='نوبت %', type='float'),
                dict(key='friday_coeff', label='ضریب جمعه', type='float'),
                dict(key='holiday_coeff', label='ضریب تعطیل', type='float'),
                dict(key='base_hours', label='ساعت ماهانه', type='int')]
        def validate(v):
            if not 1300 <= v['year'] <= 1500: return "سال معتبر نیست"
            if v['base_hours'] <= 0: return "ساعت ماهانه باید بزرگ‌تر از صفر باشد"
            return None
        return self.crud('rate_years', spec, rows,
                         lambda r: f"سال {r['year']}",
                         lambda r: f"اضافه {r['overtime_coeff']} | شب {r['night_coeff']} | "
                                   f"نوبت {r['shift_percent']}% | جمعه {r['friday_coeff']} | مبنا {r['base_hours']}",
                         "➕ نرخ جدید",
                         dict(year=self.year, overtime_coeff=1.4, night_coeff=0.35,
                              shift_percent=15, friday_coeff=0.40, holiday_coeff=1.4,
                              base_hours=220), validate)

    def v_tax(self):
        rows = self.db.q("SELECT * FROM tax_brackets WHERE company_id=? ORDER BY year DESC, from_amount", (self.cid,))
        spec = [dict(key='year', label='سال', type='int', required=True),
                dict(key='from_amount', label='از مبلغ', type='money'),
                dict(key='to_amount', label='تا مبلغ (خالی = بی‌نهایت)', type='money', blank_none=True),
                dict(key='rate', label='نرخ %', type='float')]
        def validate(v):
            if v['to_amount'] is not None and v['to_amount'] <= v['from_amount']:
                return "«تا مبلغ» باید بزرگ‌تر از «از مبلغ» باشد"
            if not 0 <= v['rate'] <= 100: return "نرخ باید ۰ تا ۱۰۰ باشد"
            return None
        return self.crud('tax_brackets', spec, rows,
                         lambda r: f"سال {r['year']} - {r['rate']:g}%",
                         lambda r: f"از {fmt(r['from_amount'])} تا "
                                   f"{fmt(r['to_amount']) if r['to_amount'] is not None else '∞'}",
                         "➕ پله جدید", dict(year=self.year), validate)

    def v_depts(self):
        rows = self.db.q("SELECT * FROM departments WHERE company_id=?", (self.cid,))
        spec = [dict(key='title', label='عنوان', required=True),
                dict(key='location', label='موقعیت'), dict(key='code', label='کد')]
        return self.crud('departments', spec, rows, lambda r: r['title'],
                         lambda r: f"{r.get('location') or '-'} • {r.get('code') or '-'}",
                         "➕ دپارتمان جدید")



# ═══════════════════════ توسعه و مهاجرت‌های تکمیلی ═══════════════════════
# ارقام سالانه در دیتابیس نگهداری می‌شوند؛ منطق محاسبه به یک سال خاص قفل نیست.
_EXTRA_MIGRATIONS = {
    'employees': [
        ('insurance_exempt', 'INTEGER DEFAULT 0'),
        ('tax_exempt', 'INTEGER DEFAULT 0'),
        ('shift_pattern', "TEXT DEFAULT 'none'"),
    ],
    'benefits': [
        ('severance_basis', 'INTEGER DEFAULT 0'),
    ],
    'rate_years': [
        ('min_daily_wage', 'INTEGER'),
        ('housing_allowance', 'INTEGER'),
        ('food_allowance', 'INTEGER'),
        ('marriage_allowance', 'INTEGER'),
        ('child_allowance', 'INTEGER'),
        ('base_year_daily', 'INTEGER'),
        ('hours_per_day', 'REAL'),
        ('weekly_hours', 'REAL'),
        ('insurance_cap_multiplier', 'REAL'),
        ('insurance_employee_rate', 'REAL'),
        ('insurance_employer_rate', 'REAL'),
        ('insurance_unemployment_rate', 'REAL'),
        ('shift_morning_evening', 'REAL'),
        ('shift_three_turn', 'REAL'),
        ('shift_morning_night', 'REAL'),
        ('eid_min_days', 'INTEGER'),
        ('eid_max_days', 'INTEGER'),
        ('mission_daily_rate', 'INTEGER'),
        ('insurance_tax_deduct_percent', 'REAL'),
    ],
    'attendances': [
        ('friday_rest_replaced', 'INTEGER DEFAULT 0'),
        ('holiday_rest_replaced', 'INTEGER DEFAULT 0'),
    ],
    'payrolls': [
        ('payment_status', "TEXT DEFAULT 'unpaid'"),
        ('payment_date', 'TEXT'),
        ('payment_ref', 'TEXT'),
        ('payment_note', 'TEXT'),
        ('friday_rest_replaced', 'INTEGER DEFAULT 0'),
        ('holiday_rest_replaced', 'INTEGER DEFAULT 0'),
    ],
}
for _tbl, _cols in _EXTRA_MIGRATIONS.items():
    MIGRATIONS.setdefault(_tbl, [])
    _known = {x[0] for x in MIGRATIONS[_tbl]}
    MIGRATIONS[_tbl].extend(x for x in _cols if x[0] not in _known)

_DB_INIT_ORIGINAL = Database.init_db

def _enhanced_db_init(self):
    _DB_INIT_ORIGINAL(self)
    # Fill only missing annual parameters. Existing non-zero administrator values remain intact.
    try:
        rows = self.q('SELECT * FROM rate_years ORDER BY year')
        for rr in rows:
            year = int(rr.get('year') or 0)
            if not year:
                continue
            changes = {}
            def get_benefit(title):
                z = self.q1('SELECT amount FROM benefits WHERE company_id=? AND year=? AND title=? ORDER BY id DESC LIMIT 1',
                            (rr.get('company_id'), year, title))
                return z.get('amount') if z else None
            def previous(key):
                z = self.q1(f'SELECT "{key}" AS v FROM rate_years WHERE company_id=? AND year<? AND "{key}" IS NOT NULL ORDER BY year DESC LIMIT 1',
                            (rr.get('company_id'), year))
                return z.get('v') if z else None
            eid = self.q1('SELECT * FROM eid_rules WHERE company_id=? AND year=? ORDER BY id DESC LIMIT 1',
                          (rr.get('company_id'), year))
            by = self.q1('SELECT amount FROM base_year_rules WHERE company_id=? AND year=? ORDER BY id LIMIT 1',
                         (rr.get('company_id'), year))
            mapping = {
                'min_daily_wage': (eid or {}).get('daily_min_wage'),
                'housing_allowance': get_benefit('حق مسکن'),
                'food_allowance': get_benefit('بن کارگری'),
                'marriage_allowance': get_benefit('حق تاهل'),
                'child_allowance': get_benefit('حق اولاد'),
                'base_year_daily': (by or {}).get('amount'),
                'hours_per_day': 7.33,
                'weekly_hours': 44.0,
                'insurance_cap_multiplier': 7.0,
                'insurance_employee_rate': 7.0,
                'insurance_employer_rate': 20.0,
                'insurance_unemployment_rate': 3.0,
                'shift_morning_evening': 10.0,
                'shift_three_turn': 15.0,
                'shift_morning_night': 22.5,
                'eid_min_days': (eid or {}).get('min_days') or 60,
                'eid_max_days': (eid or {}).get('max_days') or 90,
                'mission_daily_rate': 0,
                'insurance_tax_deduct_percent': 0.0,
            }
            for key, value in mapping.items():
                if rr.get(key) is not None:
                    continue
                if value is None:
                    value = previous(key)
                if value is None:
                    if key == 'min_daily_wage' and year == 1405:
                        value = STD['min_daily_wage']
                    elif key == 'base_year_daily' and year == 1405:
                        value = STD['base_year_daily']
                    elif key in ('housing_allowance', 'food_allowance', 'marriage_allowance', 'child_allowance') and year == 1405:
                        value = {'housing_allowance': STD['housing'], 'food_allowance': STD['food'],
                                 'marriage_allowance': STD['marriage'], 'child_allowance': STD['child_allowance']}[key]
                    elif key == 'min_daily_wage':
                        value = STD['min_daily_wage'] if not rows else 0
                    elif key == 'base_year_daily':
                        value = STD['base_year_daily'] if not rows else 0
                    elif key == 'mission_daily_rate':
                        value = 0
                    else:
                        value = mapping[key]
                changes[key] = value
            if changes:
                self.update('rate_years', rr['id'], changes)
        # Empty historical IDs are allowed; only true numeric duplicates are avoided by auto-generation.
    except Exception:
        log_error('Annual-rate migration failed:\n' + traceback.format_exc())

Database.init_db = _enhanced_db_init


def _as_float(value, default=0.0):
    try:
        if value is None or str(value).strip() == '':
            return default
        return float(norm(value))
    except Exception:
        return default


def _premium_fraction(value, default):
    """Normalize 35, 0.35, 1.35, and 35% to an extra-pay fraction."""
    v = _as_float(value, default)
    if v >= 2:
        return v / 100.0
    if v > 1:
        return v - 1.0
    return max(0.0, v)


def _overtime_multiplier(value, default=1.4):
    """Normalize overtime multiplier (1.4) or surcharge (40 / .4) to a total multiplier."""
    v = _as_float(value, default)
    if v >= 2:
        return 1.0 + (v / 100.0 if v >= 10 else v)
    if v > 1:
        return v
    return 1.0 + max(v, 0.0)


# Keep old databases compatible while letting current and future years own their values.
_CALC_INIT_ORIGINAL = PayrollCalculator.__init__
def _enhanced_calc_init(self, company, year, month):
    _CALC_INIT_ORIGINAL(self, company, year, month)
    configured_years = {int(r.get('year') or 0) for r in company.get('rate_years', [])}
    if int(year) not in configured_years:
        raise ValueError(f'تنظیمات سال {year} ثبت نشده است. ابتدا از تنظیمات، نرخ‌های همان سال را ثبت یا از سال قبل کپی و با بخشنامه جدید اصلاح کنید.')
    rate = self.rate or {}
    def chosen(key, fallback):
        v = rate.get(key)
        return fallback if v is None or v == '' else v
    eid_rows = self._nearest(company.get('eid_rules', []), year)
    eid = eid_rows[0] if eid_rows else {}
    self.min_daily_wage = int(chosen('min_daily_wage', eid.get('daily_min_wage') or
                                     (STD['min_daily_wage'] if year >= 1405 else 0)) or 0)
    if not self.min_daily_wage:
        self.min_daily_wage = int(eid.get('daily_min_wage') or STD['min_daily_wage'])
    self.hours_per_day = max(_as_float(chosen('hours_per_day', STD['hours_per_day']), STD['hours_per_day']), 1.0)
    cap_multiplier = max(_as_float(chosen('insurance_cap_multiplier', 7), 7), 0)
    self.insurance_cap = rnd(cap_multiplier * self.min_daily_wage * self.dim)
    self.insurance_rate = _as_float(chosen('insurance_employee_rate', company.get('insurance_rate', 7)), 7)
    er = chosen('insurance_employer_rate', None)
    ur = chosen('insurance_unemployment_rate', None)
    if er is not None:
        self.employer_insurance_rate = _as_float(er, 20) + _as_float(ur, 3)
    else:
        self.employer_insurance_rate = _as_float(company.get('employer_insurance_rate', 23), 23)
    self.overtime_coeff = _overtime_multiplier(rate.get('overtime_coeff'), 1.4)
    self.night_coeff = _premium_fraction(rate.get('night_coeff'), 0.35)
    self.friday_coeff = _premium_fraction(rate.get('friday_coeff'), 0.40)
    self.holiday_coeff = _premium_fraction(rate.get('holiday_coeff'), 0.40)
    self.shift_morning_evening = _as_float(chosen('shift_morning_evening', 10), 10)
    self.shift_three_turn = _as_float(chosen('shift_three_turn', 15), 15)
    self.shift_morning_night = _as_float(chosen('shift_morning_night', 22.5), 22.5)
    self.eid_min_days = int(chosen('eid_min_days', eid.get('min_days') or 60) or 60)
    self.eid_max_days = int(chosen('eid_max_days', eid.get('max_days') or 90) or 90)
    self.mission_daily_rate = max(0, int(chosen('mission_daily_rate', 0) or 0))
    self.ins_tax_deduct_pct = min(max(_as_float(rate.get('insurance_tax_deduct_percent'), 0.0), 0.0), 100.0)
    annual_benefits = {
        'حق مسکن': rate.get('housing_allowance'),
        'بن کارگری': rate.get('food_allowance'),
        'حق تاهل': rate.get('marriage_allowance'),
        'حق اولاد': rate.get('child_allowance'),
    }
    for benefit in self.benefits:
        amount = annual_benefits.get(benefit.get('title'))
        if amount is not None:
            benefit['amount'] = max(0, int(amount))

PayrollCalculator.__init__ = _enhanced_calc_init


def _enhanced_base_year_bonus(self, emp, work_days):
    service = self.service_years(emp)
    if service < 1:
        return 0
    matching = [r for r in self.base_year_rules
                if (r.get('min_service') or 1) <= service <= (r.get('max_service') or 999)]
    # A broad 1..20-year row is the ordinary annual rate; a more specific row can override it.
    specialized = [r for r in matching
                   if int(r.get('min_service') or 1) > 1 or int(r.get('max_service') or 999) < 20]
    if specialized:
        chosen_rule = sorted(specialized, key=lambda r: (int(r.get('min_service') or 1), int(r.get('max_service') or 999)))[-1]
        daily = chosen_rule.get('amount')
    else:
        daily = self.rate.get('base_year_daily')
        if daily is None and matching:
            daily = matching[0].get('amount')
    if daily is None:
        daily = STD['base_year_daily']
    return rnd(max(0, _as_float(daily)) * max(0, _as_float(work_days)))

PayrollCalculator.base_year_bonus = _enhanced_base_year_bonus


def _enhanced_compute_salary(self, emp, att, installments=None, bonuses=None, deductions=None):
    """Payroll engine: separates gross pay, taxable pay, insured pay and deductions."""
    installments = installments or []
    bonuses = bonuses or []
    deductions = deductions or []
    wd = max(0.0, _as_float(att.get('work_days')))
    dim = max(1, int(self.dim))
    daily = max(0, int(emp.get('daily_salary') or self.min_daily_wage or 0))
    base = rnd(daily * wd)

    def hours(hk, mk):
        return max(0.0, _as_float(att.get(hk)) + _as_float(att.get(mk)) / 60.0)

    ot_h = hours('overtime_hours', 'overtime_minutes')
    ng_h = hours('night_hours', 'night_minutes')
    ab_h = hours('absent_hours', 'absent_minutes')
    fd_h = max(0.0, _as_float(att.get('friday_hours')))
    hl_h = max(0.0, _as_float(att.get('holiday_hours')))
    md_d = max(0.0, _as_float(att.get('mission_days')))
    shift_pattern = str(emp.get('shift_pattern') or 'none')
    sp = max(0.0, _as_float(att.get('shift_percent')))
    if shift_pattern == 'none':
        sp = 0.0
    elif sp == 0:
        sp = {
            'morning_evening': self.shift_morning_evening,
            'morning_evening_night': self.shift_three_turn,
            'morning_night': self.shift_morning_night,
            'evening_night': self.shift_morning_night,
        }.get(shift_pattern, 0.0)

    daily_fixed = daily
    if self.service_years(emp) >= 1:
        by_daily = self.rate.get('base_year_daily')
        if by_daily is None:
            matching = [r for r in self.base_year_rules
                        if (r.get('min_service') or 1) <= self.service_years(emp) <= (r.get('max_service') or 999)]
            by_daily = matching[-1].get('amount') if matching else STD['base_year_daily']
        daily_fixed += max(0, int(by_daily or 0))
    hourly = daily_fixed / self.hours_per_day
    overtime = rnd(hourly * self.overtime_coeff * ot_h)
    night = 0 if shift_pattern != 'none' else rnd(hourly * self.night_coeff * ng_h)
    absent = rnd(hourly * ab_h)
    shift = rnd(daily_fixed * wd * sp / 100.0) if sp > 0 else 0
    friday = rnd(hourly * (1.0 + self.friday_coeff) * fd_h)
    holiday = rnd(hourly * (1.0 + self.holiday_coeff) * hl_h)
    mission_daily = self.mission_daily_rate if self.mission_daily_rate > 0 else daily_fixed
    mission = rnd(mission_daily * md_d)

    items = []
    total_items = 0
    taxable_items = 0
    insured_items = 0
    non_taxable_items = 0

    def add_item(name, amount, taxable=True, insurable=True):
        nonlocal total_items, taxable_items, insured_items, non_taxable_items
        amount = rnd(max(0, _as_float(amount)))
        if not amount:
            return
        items.append({'name': name, 'amount': amount,
                      'taxable': bool(taxable), 'insurable': bool(insurable)})
        total_items += amount
        if taxable:
            taxable_items += amount
        else:
            non_taxable_items += amount
        if insurable:
            insured_items += amount

    prorate = min(max(wd, 0.0), float(dim)) / float(dim)
    for b in self.benefits:
        title = b.get('title') or 'مزایای دیگر'
        ctype = b.get('calc_type') or 'fixed'
        if ctype == 'child' or title == 'حق اولاد':
            continue
        if self._is_excepted(b.get('id'), emp, emp.get('dept_id')):
            continue
        if (ctype == 'marital' or title == 'حق تاهل') and not emp.get('marital'):
            continue
        amount = max(0, _as_float(b.get('amount'))) * prorate
        if ctype == 'percent':
            amount = base * max(0, _as_float(b.get('amount'))) / 100.0
        add_item(title, amount, bool(b.get('taxable', 1)), bool(b.get('insurable', 1)))

    for b in bonuses:
        if (b.get('emp_id') == emp.get('id') and b.get('year') == self.year
                and b.get('month') == self.month):
            add_item('پاداش' + ((' - ' + b.get('reason', '')) if b.get('reason') else ''),
                     b.get('amount', 0), bool(b.get('taxable', 1)), bool(b.get('insurable', 1)))

    base_year = self.base_year_bonus(emp, wd)
    add_item('پایه سنوات', base_year, True, True)

    child_count = max(0, int(emp.get('child_count') or 0))
    if child_count:
        child_per = 0
        child_insurable = False
        child_taxable = True
        for b in self.benefits:
            if b.get('title') == 'حق اولاد' or b.get('calc_type') == 'child':
                child_per = max(0, _as_float(b.get('amount')))
                child_insurable = bool(b.get('insurable', 0))
                child_taxable = bool(b.get('taxable', 1))
                break
        if child_per == 0 and self.rate.get('child_allowance') is None:
            child_per = STD['child_allowance']
        add_item('حق اولاد', child_per * child_count * prorate,
                 child_taxable, child_insurable)

    deduction_total = rnd(sum(max(0, _as_float(d.get('amount'))) for d in deductions
                              if d.get('emp_id') == emp.get('id')
                              and d.get('year') == self.year and d.get('month') == self.month))

    gross = rnd(base + overtime + night + shift + friday + holiday + mission + total_items)
    taxable = max(0, rnd(base + overtime + night + shift + friday + holiday + taxable_items))
    insurable = max(0, rnd(base + overtime + night + shift + friday + holiday + insured_items))
    insurance_exempt = bool(emp.get('insurance_exempt'))
    tax_exempt = bool(emp.get('tax_exempt'))
    ins_emp = 0 if insurance_exempt else self.insurance(insurable, self.insurance_rate)
    ins_er = 0 if insurance_exempt else self.insurance(insurable, self.employer_insurance_rate)
    # سهم بیمه کارگر به درصد تعیین‌شده در تنظیمات (پیش‌فرض صفر) از مبنای مالیات کسر می‌شود.
    ins_tax_deduction = rnd(ins_emp * self.ins_tax_deduct_pct / 100.0) if ins_emp > 0 else 0
    taxable_after = max(0, taxable - ins_tax_deduction)
    tax = 0 if tax_exempt else self.monthly_tax(taxable_after)

    # ═══════════ اقساط وام — با احترام کامل به وضعیت‌ها ═══════════
    loan_total, loan_ids, loan_details = 0, [], []
    for inst in installments:
        if inst.get('emp_id') != emp.get('id'):
            continue
        if inst.get('is_paid'):
            continue
        status = inst.get('status') or 'pending'
        if status in ('paid', 'skipped', 'waived'):
            continue
        eff_y = inst.get('due_year')
        eff_m = inst.get('due_month')
        if eff_y != self.year or eff_m != self.month:
            continue

        amt = _as_float(inst.get('amount'))
        loan_total += amt
        loan_ids.append(inst.get('id'))
        loan_details.append({
            'installment_id': inst.get('id'),
            'no': inst.get('installment_no'),
            'amount': rnd(amt),
            'original_due': f"{inst.get('original_due_year') or eff_y}/"
                            f"{(inst.get('original_due_month') or eff_m):02d}",
            'defer_count': inst.get('defer_count') or 0,
        })
    loan_total = rnd(loan_total)

    net = rnd(gross - ins_emp - tax - absent - loan_total - deduction_total)

    return {
        'gross': gross, 'net': net,
        'insurance_emp': ins_emp, 'insurance_er': ins_er, 'tax': tax,
        'overtime': overtime, 'shift': shift, 'night': night,
        'mission': mission, 'friday_work': friday, 'holiday_work': holiday,
        'absent_ded': absent,
        'loan_install': loan_total,
        'loan_inst_ids': loan_ids,
        'loan_details': loan_details,
        'benefits_list': items,
        'base_salary_monthly': base,
        'work_days': wd,
        'overtime_hours': ot_h, 'night_hours': ng_h,
        'absent_hours': ab_h, 'mission_days': md_d,
        'friday_hours': fd_h, 'holiday_hours': hl_h,
        'bonus_amount': sum(i['amount'] for i in items if i['name'].startswith('پاداش')),
        'deduction_amount': deduction_total,
        'base_year_amount': base_year,
        'taxable_gross': taxable_after,
        'insurance_tax_deduction': ins_tax_deduction,
        'friday_rest_replaced': int(bool(att.get('friday_rest_replaced'))),
        'holiday_rest_replaced': int(bool(att.get('holiday_rest_replaced'))),
        'non_taxable_amount': non_taxable_items,
        'insured_base': insurable,
    }

PayrollCalculator.compute_salary = _enhanced_compute_salary



def _last_wage_basis_monthly(calc, emp):
    """مبنای مزد ماهانه برای عیدی و سنوات؛ مزایای رفاهی فقط با علامت‌گذاری صریح وارد می‌شوند."""
    daily = max(0, _as_float(emp.get('daily_salary')))
    base_year = calc.base_year_bonus(emp, 30)
    monthly_basis = daily * 30 + base_year
    for b in calc.benefits:
        if not bool(b.get('severance_basis', 0)):
            continue
        if not bool(b.get('monthly', 1)):
            continue
        title = str(b.get('title') or '')
        ctype = str(b.get('calc_type') or 'fixed')
        if title == 'حق اولاد' or ctype == 'child':
            continue
        if (title == 'حق تاهل' or ctype == 'marital') and not emp.get('marital'):
            continue
        if calc._is_excepted(b.get('id'), emp, emp.get('dept_id')):
            continue
        amount = max(0, _as_float(b.get('amount')))
        if ctype == 'percent':
            amount = daily * 30 * amount / 100.0
        monthly_basis += amount
    return rnd(max(0, monthly_basis))


def calc_eid(emp, year, company):
    calc = PayrollCalculator(company, year, 1)
    work_days = max(0.0, _year_work_days(emp, year, company))
    if work_days <= 0:
        return 0
    monthly_basis = _last_wage_basis_monthly(calc, emp)
    last_daily_wage = monthly_basis / 30.0
    entitlement_days = max(0, int(calc.eid_min_days or 60))
    cap_days = max(entitlement_days, int(calc.eid_max_days or 90))
    daily_min = max(0, int(calc.min_daily_wage or STD['min_daily_wage']))
    # قانون عیدی: ۶۰ روز آخرین مزد، با سقف ۹۰ روز حداقل مزد روزانه قانونی؛ کارکرد کمتر تناسبی است.
    yearly_entitlement = min(last_daily_wage * entitlement_days, daily_min * cap_days)
    return rnd(yearly_entitlement * min(work_days / float(days_in_year(year)), 1.0))


def calc_severance(emp, year, company):
    calc = PayrollCalculator(company, year, 1)
    work_days = max(0.0, _year_work_days(emp, year, company))
    if work_days <= 0:
        return 0
    monthly_basis = _last_wage_basis_monthly(calc, emp)
    return rnd(monthly_basis * min(work_days / float(days_in_year(year)), 1.0))


def _enhanced_accounting_entries(pid, year, month, emp, r):
    rows = accounting_entries.__wrapped__(pid, year, month, emp, r) if hasattr(accounting_entries, '__wrapped__') else _ACCOUNTING_ENTRIES_ORIGINAL(pid, year, month, emp, r)
    if r.get('deduction_amount', 0) > 0:
        rows.append(dict(payroll_id=pid, entry_date=f'{year}-{month:02d}-01',
                         account_code='210107', account_name='سایر کسورات پرداختنی',
                         debit=0, credit=r['deduction_amount'],
                         description='کسورات ثبت‌شده برای دوره حقوق'))
    return rows

_ACCOUNTING_ENTRIES_ORIGINAL = accounting_entries
accounting_entries = _enhanced_accounting_entries


# نسخه منعطف و قابل جست‌وجوی تمام فهرست‌های کشویی.
def dd(label, options, value=None, on_select=None, width=None, expand=False,
       size=12, hint=None):
    Opt = getattr(ft, 'DropdownOption', None) or ft.dropdown.Option
    val_str = None if value is None else str(value)
    valid_keys = {str(k) for k, _ in options}
    if val_str is not None and val_str not in valid_keys:
        val_str = None
    args = dict(label=label, value=val_str, width=width, expand=expand,
                text_size=size, label_style=ft.TextStyle(size=size - 1),
                content_padding=pad_sym(12, 10), dense=True, hint_text=hint,
                options=[Opt(key=str(k), text=str(t)) for k, t in options],
                enable_filter=True, enable_search=True, editable=True,
                **_border_kwargs(10))
    if on_select:
        args['on_select' if 'on_select' in _params(ft.Dropdown) else 'on_change'] = on_select
    return K(ft.Dropdown, **args)


# تنظیمات سالانه کامل‌تر از نسخه اولیه.
def _app_v_rates(self):
    rows = self.db.q('SELECT * FROM rate_years WHERE company_id=? ORDER BY year DESC, id DESC', (self.cid,))
    spec = [
        dict(key='year', label='سال قانون کار', type='int', required=True),
        dict(key='min_daily_wage', label='حداقل مزد روزانه (ریال)', type='money', required=True),
        dict(key='base_year_daily', label='پایه سنوات روزانه (ریال)', type='money'),
        dict(key='housing_allowance', label='حق مسکن ماهانه (ریال)', type='money'),
        dict(key='food_allowance', label='بن کارگری ماهانه (ریال)', type='money'),
        dict(key='marriage_allowance', label='حق تأهل ماهانه (ریال)', type='money'),
        dict(key='child_allowance', label='حق اولاد هر فرزند (ریال)', type='money'),
        dict(key='overtime_coeff', label='ضریب کل اضافه‌کاری (۱٫۴)', type='float'),
        dict(key='night_coeff', label='فوق‌العاده شب‌کاری (۰٫۳۵ یا ۳۵)', type='float'),
        dict(key='friday_coeff', label='فوق‌العاده جمعه‌کاری (۰٫۴ یا ۴۰)', type='float'),
        dict(key='holiday_coeff', label='فوق‌العاده تعطیل‌کاری (۰٫۴ یا ۴۰)', type='float'),
        dict(key='shift_morning_evening', label='نوبت صبح و عصر (%)', type='float'),
        dict(key='shift_three_turn', label='نوبت صبح/عصر/شب (%)', type='float'),
        dict(key='shift_morning_night', label='نوبت صبح و شب یا عصر و شب (%)', type='float'),
        dict(key='base_hours', label='ساعت ماهانه مبنا', type='int'),
        dict(key='hours_per_day', label='ساعت روزانه محاسبات (معمولاً ۷٫۳۳)', type='float'),
        dict(key='weekly_hours', label='ساعت هفتگی قانونی', type='float'),
        dict(key='insurance_employee_rate', label='بیمه سهم کارگر (%)', type='float'),
        dict(key='insurance_employer_rate', label='بیمه سهم کارفرما بدون بیکاری (%)', type='float'),
        dict(key='insurance_unemployment_rate', label='بیمه بیکاری (%)', type='float'),
        dict(key='insurance_cap_multiplier', label='ضریب سقف دستمزد بیمه', type='float'),
        dict(key='insurance_tax_deduct_percent', label='درصدی از بیمه سهم کارگر که از مبنای مالیات کسر می‌شود (۰ تا ۱۰۰؛ پیش‌فرض ۰)', type='float'),
        dict(key='eid_min_days', label='روز مزد مبنای عیدی (معمولاً ۶۰)', type='int'),
        dict(key='eid_max_days', label='سقف روز مزد عیدی (معمولاً ۹۰)', type='int'),
        dict(key='mission_daily_rate', label='نرخ روزانه مأموریت؛ صفر=مزد روزانه', type='money'),
    ]
    latest = next((r for r in rows if r.get('year', 0) <= self.year), rows[0] if rows else {})
    if latest:
        defaults = {f['key']: latest.get(f['key']) for f in spec}
    else:
        defaults = {}
    defaults.update(dict(
        year=self.year, min_daily_wage=STD['min_daily_wage'], base_year_daily=STD['base_year_daily'],
        housing_allowance=STD['housing'], food_allowance=STD['food'],
        marriage_allowance=STD['marriage'], child_allowance=STD['child_allowance'],
        overtime_coeff=1.4, night_coeff=0.35, friday_coeff=0.4, holiday_coeff=0.4,
        shift_morning_evening=10, shift_three_turn=15, shift_morning_night=22.5,
        base_hours=220, hours_per_day=7.33, weekly_hours=44,
        insurance_employee_rate=7, insurance_employer_rate=20,
        insurance_unemployment_rate=3, insurance_cap_multiplier=7,
        eid_min_days=60, eid_max_days=90, mission_daily_rate=0,
        insurance_tax_deduct_percent=0))
    # Keep explicit values from the nearest existing year, except its year.
    if latest:
        for f in spec:
            key = f['key']
            if key != 'year' and latest.get(key) is not None:
                defaults[key] = latest[key]
    defaults['year'] = self.year

    def validate(v, current=None):
        if not 1300 <= int(v.get('year') or 0) <= 1500:
            return 'سال معتبر نیست.'
        current_id = current.get('id') if current else None
        if current_id:
            other = self.db.q1('SELECT id FROM rate_years WHERE company_id=? AND year=? AND id<>?',
                               (self.cid, v['year'], current_id))
        else:
            other = self.db.q1('SELECT id FROM rate_years WHERE company_id=? AND year=?',
                               (self.cid, v['year']))
        if other:
            return 'برای این سال از قبل تنظیمات ثبت شده است؛ همان ردیف را ویرایش کنید.'
        if v['min_daily_wage'] <= 0:
            return 'حداقل مزد روزانه باید بیشتر از صفر باشد.'
        if v['base_hours'] <= 0 or v['hours_per_day'] <= 0 or v['weekly_hours'] <= 0:
            return 'ساعات مبنا باید بیشتر از صفر باشند.'
        for key in ('insurance_employee_rate','insurance_employer_rate','insurance_unemployment_rate'):
            if not 0 <= _as_float(v.get(key)) <= 100:
                return 'درصد بیمه باید بین صفر تا ۱۰۰ باشد.'
        if not 0 <= _as_float(v.get('insurance_tax_deduct_percent')) <= 100:
            return 'درصد کسر بیمه از مبنای مالیات باید بین صفر تا ۱۰۰ باشد.'
        if v['eid_min_days'] <= 0 or v['eid_max_days'] < v['eid_min_days']:
            return 'روزهای عیدی را بررسی کنید.'
        for key in ('housing_allowance','food_allowance','marriage_allowance','child_allowance','base_year_daily','mission_daily_rate'):
            if _as_float(v.get(key)) < 0: return 'مبالغ سالانه نمی‌توانند منفی باشند.'
        return None

    # Use all rows via the established CRUD editor; annual benefit fields are consumed directly by the calculator.
    return self.crud('rate_years', spec, rows,
                     lambda r: f"سال {r['year']} | حداقل مزد روزانه {fmt(r.get('min_daily_wage') or 0)} ریال",
                     lambda r: f"مسکن {fmt(r.get('housing_allowance') or 0)} | بن {fmt(r.get('food_allowance') or 0)} | سنوات {fmt(r.get('base_year_daily') or 0)} | کسر بیمه از مالیات {_as_float(r.get('insurance_tax_deduct_percent')):g}٪",
                     'افزودن سال جدید', defaults, validate)

App.v_rates = _app_v_rates


def _app_v_base_year_rules(self):
    rows = self.db.q('SELECT * FROM base_year_rules WHERE company_id=? ORDER BY year DESC,min_service', (self.cid,))
    spec = [dict(key='year', label='سال', type='int', required=True),
            dict(key='min_service', label='حداقل سابقه کامل (سال)', type='int', required=True),
            dict(key='max_service', label='حداکثر سابقه کامل (سال)', type='int', required=True),
            dict(key='amount', label='پایه سنوات روزانه (ریال)', type='money', required=True)]
    def validate(v):
        if not 1300 <= v['year'] <= 1500: return 'سال معتبر نیست.'
        if v['min_service'] < 1 or v['max_service'] < v['min_service']: return 'بازه سابقه معتبر نیست.'
        if v['amount'] < 0: return 'مبلغ نمی‌تواند منفی باشد.'
        return None
    return self.crud('base_year_rules', spec, rows,
        lambda r: f"سال {r['year']} | سابقه {r['min_service']} تا {r['max_service']} سال",
        lambda r: f"روزانه {fmt(r['amount'])} ریال", 'قاعده پایه سنوات',
        dict(year=self.year, min_service=1, max_service=20, amount=STD['base_year_daily']), validate)

App.v_base_year_rules = _app_v_base_year_rules


def _app_v_eid_rules(self):
    rows = self.db.q('SELECT * FROM eid_rules WHERE company_id=? ORDER BY year DESC', (self.cid,))
    spec = [dict(key='year', label='سال', type='int', required=True),
            dict(key='min_days', label='روز مزد مبنای عیدی', type='int', required=True),
            dict(key='max_days', label='سقف روز مزد عیدی', type='int', required=True),
            dict(key='daily_min_wage', label='حداقل مزد روزانه (ریال)', type='money', required=True)]
    def validate(v):
        if not 1300 <= v['year'] <= 1500: return 'سال معتبر نیست.'
        if v['min_days'] <= 0 or v['max_days'] < v['min_days']: return 'روزهای عیدی معتبر نیست.'
        if v['daily_min_wage'] <= 0: return 'حداقل مزد روزانه معتبر نیست.'
        return None
    return self.crud('eid_rules', spec, rows,
        lambda r: f"سال {r['year']} | عیدی {r['min_days']} تا {r['max_days']} روز",
        lambda r: f"حداقل مزد روزانه {fmt(r['daily_min_wage'])} ریال", 'قاعده عیدی',
        dict(year=self.year, min_days=60, max_days=90, daily_min_wage=STD['min_daily_wage']), validate)

App.v_eid_rules = _app_v_eid_rules


def _app_v_settings(self):
    def copy_year(e):
        src = self.db.previous_settings_year(self.cid, self.year)
        if not src:
            self.toast(f'سال قبل از {self.year} تنظیماتی ندارد', True); return
        def go():
            n = self.db.copy_year(self.cid, src, self.year)
            self.toast(f'تنظیمات {src} به {self.year} کپی شد ({n} مورد)' if n else
                       f'برای سال {self.year} داده‌ای کپی نشد؛ احتمالاً قبلاً وجود دارد.', n == 0)
            self.refresh()
        self.confirm(f'تمام تنظیمات سال {src} به سال {self.year} کپی شود؟', go, 'کپی تنظیمات', False)
    def tile(icon, title, subtitle, handler):
        return card(ft.Row([
            ft.Icon(icon, color=T()['accent'], size=20),
            ft.Column([txt(title, 12, True), txt(subtitle, 9, color=T()['muted'])], spacing=2, expand=True),
            ft.Icon(_ic('CHEVRON_LEFT'), color=T()['muted'], size=16),
        ], spacing=8), padding=10, on_click=lambda e: self.push(title, handler))
    return ft.ListView([
        self.period_bar(self.refresh, False),
        tile(_ic('PERCENT'), 'نرخ‌های سالانه قانون کار', 'مزد، مزایا، بیمه، ساعات و ضرایب؛ پیش از محاسبه هر سال با بخشنامه همان سال تطبیق دهید', self.v_rates),
        tile(_ic('CARD_GIFTCARD'), 'مزایای سالانه', 'ویرایش حق مسکن، بن، تأهل، اولاد و مزایای اختصاصی', self.v_benefits),
        tile(_ic('ACCOUNT_BALANCE'), 'پله‌های مالیات حقوق', 'تعریف پله‌های پلکانی هر سال', self.v_tax),
        tile(_ic('STAIRS'), 'قواعد پایه سنوات', 'بازه سابقه و مبلغ روزانه هر سال', self.v_base_year_rules),
        tile(_ic('CELEBRATION'), 'قواعد عیدی سالانه', 'روزهای مبنا و سقف عیدی هر سال', self.v_eid_rules),
        tile(_ic('APARTMENT'), 'دپارتمان‌ها', 'واحدهای سازمانی', self.v_depts),
        card(ft.Row([ft.Icon(_ic('CONTENT_COPY'), color=T()['accent'], size=20),
            ft.Column([txt('کپی تنظیمات از سال قبل', 12, True), txt('ساخت سال جدید بر پایه سال قبل', 9, color=T()['muted'])], spacing=2, expand=True),
            ft.Icon(_ic('CHEVRON_LEFT'), color=T()['muted'], size=16)], spacing=8), padding=10, on_click=copy_year),
    ], spacing=6, expand=True, padding=pad_only(bottom=20))

App.v_settings = _app_v_settings


def _app_contract_view(self, emp):
    Contract(self, emp).open()

App.contract_view = _app_contract_view


# انتقال فایل به پنل اشتراک‌گذاری سیستم‌عامل تا کاربر بتواند PDF را به پیام‌رسان یا چاپگر بفرستد.
def _app_file_dialog(self, path, title='فایل آماده است', count=None):
    label = f'{title} ({count} فیش)' if count else title
    def do_open(ev):
        if not open_file(path):
            self.toast('این دستگاه بازکردن مستقیم فایل را پشتیبانی نکرد؛ از «اشتراک‌گذاری» استفاده کنید.', True)
    def do_copy(ev):
        try:
            f = getattr(self.page, 'set_clipboard', None)
            if callable(f): f(path)
            else: ft.Clipboard().set(path)
            self.toast('مسیر فایل کپی شد')
        except Exception:
            self.toast('کپی مسیر ممکن نشد', True)
    async def do_share(ev):
        try:
            Share = getattr(ft, 'Share', None)
            ShareFile = getattr(ft, 'ShareFile', None)
            if Share is None or ShareFile is None:
                self.toast('اشتراک‌گذاری مستقیم در نسخه فعلی Flet موجود نیست؛ فایل در مسیر نمایش‌داده‌شده ذخیره شده است.', True)
                return
            service = getattr(self, '_share_service', None)
            if service is None:
                service = Share()
                services = getattr(self.page, 'services', None)
                if services is not None and service not in services:
                    services.append(service)
                self._share_service = service
            result = service.share_files([ShareFile.from_path(path)], title=label, text=label)
            if inspect.isawaitable(result):
                await result
        except Exception:
            log_error(traceback.format_exc())
            self.toast('اشتراک‌گذاری انجام نشد؛ فایل ذخیره شده و می‌توانید آن را از مسیر بالا بردارید.', True)
    d = ft.AlertDialog(
        modal=True, title=ft.Text(label, size=13),
        content=ft.Container(ft.Column([
            txt('فایل ساخته و ذخیره شد. برای ارسال به پیام‌رسان یا چاپگر گوشی، اشتراک‌گذاری را بزنید.', 11),
            txt('مسیر فایل:', 10, color=T()['muted']),
            ft.Container(txt(path, 10, selectable=True), bgcolor=T()['bg'], padding=8, border_radius=8),
        ], spacing=8, tight=True), width=min((self.page.width or 400) - 32, 400)),
        actions=[tbtn('📋 کپی مسیر', do_copy),
                 gbtn('📤 اشتراک‌گذاری / چاپ', _ic('SHARE'), do_share, T()['primary']),
                 gbtn('📂 باز کردن', _ic('OPEN_IN_NEW'), do_open, T()['success']),
                 tbtn('بستن', lambda e: self.close_dlg(d))])
    self.open_dlg(d)

App.file_dialog = _app_file_dialog


# انتخاب عکس با خواندن bytes؛ در مرورگر و گوشی همیشه مسیر فایل محلی در دسترس نیست.
def _compress_image_bytes(data, max_size=(500, 500), quality=82):
    if Image is not None:
        try:
            img = Image.open(io.BytesIO(data))
            img.thumbnail(max_size)
            buf = io.BytesIO()
            img.convert('RGB').save(buf, format='JPEG', quality=quality, optimize=True)
            return buf.getvalue()
        except Exception:
            pass
    return data


def _picked_bytes(file_obj):
    data = getattr(file_obj, 'bytes', None)
    if data:
        return bytes(data)
    p = getattr(file_obj, 'path', None)
    if p and os.path.isfile(p):
        with open(p, 'rb') as f:
            return f.read()
    return None


def _image_data_uri(data):
    # If Pillow is unavailable, keep the original file and its correct MIME type.
    if data.startswith(b'\x89PNG\r\n\x1a\n'):
        mime = 'image/png'
    elif data.startswith(b'\xff\xd8\xff'):
        mime = 'image/jpeg'
    elif len(data) >= 12 and data[:4] == b'RIFF' and data[8:12] == b'WEBP':
        mime = 'image/webp'
    else:
        mime = 'image/jpeg'
    return 'data:' + mime + ';base64,' + base64.b64encode(data).decode('ascii')


def _attach_picker(page, picker):
    # Flet جدید FilePicker را در services می‌خواهد؛ نسخه‌های قدیمی آن را در overlay می‌گذارند.
    try:
        services = getattr(page, 'services', None)
        if services is not None and picker not in services:
            services.append(picker)
            return
    except Exception:
        pass
    try:
        if picker not in page.overlay:
            page.overlay.append(picker)
    except Exception:
        pass


async def _app_pick_photo(self, emp_id):
    try:
            picker = K(ft.FilePicker, on_result=lambda e: self._on_photo_picked(e, emp_id))
            _attach_picker(self.page, picker)
            self.page.update()
            result = picker.pick_files(allow_multiple=False,
                                       allowed_extensions=['jpg','jpeg','png','webp'], with_data=True)
            if inspect.isawaitable(result):
                result = await result
            if result:
                files = result if isinstance(result, (list, tuple)) else getattr(result, 'files', [])
                if files:
                    self._store_employee_photo(emp_id, files[0])
    except Exception:
        log_error(traceback.format_exc())
        self.toast('انتخاب عکس انجام نشد. دسترسی فایل‌ها و نسخه Flet را بررسی کنید.', True)


def _app_store_employee_photo(self, emp_id, file_obj):
    try:
        data = _picked_bytes(file_obj)
        if not data:
            self.toast('محتوای عکس از انتخابگر دریافت نشد.', True); return
        data = _compress_image_bytes(data)
        self.db.update('employees', emp_id, {'photo': _image_data_uri(data)})
        self.toast('عکس پرسنل ذخیره شد')
        self.refresh()
    except Exception:
        log_error(traceback.format_exc()); self.toast('ذخیره عکس ناموفق بود.', True)


def _app_photo_picked(self, e, emp_id):
    files = getattr(e, 'files', None) or []
    if files:
        self._store_employee_photo(emp_id, files[0])

App._pick_photo = _app_pick_photo
App._store_employee_photo = _app_store_employee_photo
App._on_photo_picked = _app_photo_picked


async def _app_pick_logo(self):
    try:
        picker = K(ft.FilePicker, on_result=self._on_logo_picked)
        _attach_picker(self.page, picker)
        self.page.update()
        result = picker.pick_files(allow_multiple=False,
                                   allowed_extensions=['jpg','jpeg','png','webp'], with_data=True)
        if inspect.isawaitable(result):
            result = await result
        if result:
            files = result if isinstance(result, (list, tuple)) else getattr(result, 'files', [])
            if files:
                self._store_company_logo(files[0])
    except Exception:
        log_error(traceback.format_exc()); self.toast('انتخاب لوگو انجام نشد.', True)


def _app_store_company_logo(self, file_obj):
    try:
        data = _picked_bytes(file_obj)
        if not data:
            self.toast('محتوای فایل لوگو دریافت نشد.', True); return
        data = _compress_image_bytes(data, (600, 400), 88)
        self.db.update('companies', self.cid, {'logo': _image_data_uri(data)})
        self.toast('لوگوی شرکت ذخیره شد')
        self.refresh()
    except Exception:
        log_error(traceback.format_exc()); self.toast('ذخیره لوگو ناموفق بود.', True)


def _app_logo_picked(self, e):
    files = getattr(e, 'files', None) or []
    if files:
        self._store_company_logo(files[0])

App._pick_logo = _app_pick_logo
App._store_company_logo = _app_store_company_logo
App._on_logo_picked = _app_logo_picked


# فیش حقوقی رسمی A4 با جدول طبقه‌بندی‌شده و صفحه‌بندی واقعی.
def build_pdf(path, company, slips):
    """فیش حقوقی A4 — کلاسیک، رنگ‌بندی‌شده، با قاب دور برگه و ساعت/دقیقه فارسی."""
    pdf, _ = _pdf_init((210, 297))

    W, M = 210, 12
    CW = W - 2 * M

    # ─── پالت رنگی کلاسیک ───
    NAVY    = (30, 58, 95)
    NAVY_L  = (60, 95, 140)
    GOLD    = (184, 134, 11)
    GOLD_BG = (255, 248, 220)
    WHITE   = (255, 255, 255)
    ROW_ALT = (248, 250, 253)
    ROW_HD  = (232, 240, 248)
    SOFT_BG = (244, 248, 252)
    BORDER  = (95, 115, 140)
    BORDER2 = (55, 80, 110)
    TXT     = (20, 30, 45)
    MUTED   = (90, 105, 125)
    GREEN   = (22, 110, 70)
    RED     = (160, 35, 35)
    BLUE    = (25, 70, 130)
    PURPLE  = (85, 40, 120)
    ORANGE  = (170, 85, 20)

    # ─── مقیاس فونت ───
    F_TITLE, F_SUB = 14, 10.5
    F_HEAD, F_BODY, F_SMALL, F_TINY = 9.5, 8.8, 8.2, 7.5
    F_NET = 12.5

    PAD_X, PAD_Y = 2.5, 1.5

    # ═══════════ ابزارهای پایه ═══════════
    def put(x, y, w, h, text, align='R', size=F_BODY, color=TXT):
        pdf.set_xy(x, y)
        pdf.set_font('F', size=size)
        pdf.set_text_color(*color)
        yy = y + (h - size * 0.42) / 2
        pdf.set_xy(x, yy)
        pdf.cell(w, size * 0.42, rtl(str(text)), border=0, align=align)

    def box(x, y, w, h, fill=None, border=1, lw=0.35, bc=None):
        if fill:
            pdf.set_fill_color(*fill)
            pdf.rect(x, y, w, h, 'F')
        if border:
            pdf.set_draw_color(*(bc or BORDER))
            pdf.set_line_width(lw)
            pdf.rect(x, y, w, h, 'D')

    def cell(x, y, w, h, text, align='R', size=F_BODY, color=TXT,
             fill=None, border=1, bc=None, lw=0.35):
        box(x, y, w, h, fill=fill, border=border, lw=lw, bc=bc)
        if text != '':
            put(x + PAD_X, y, w - 2 * PAD_X, h, text,
                align=align, size=size, color=color)

    def hline(x1, x2, y, color=None, lw=0.35):
        pdf.set_draw_color(*(color or BORDER))
        pdf.set_line_width(lw)
        pdf.line(x1, y, x2, y)

    def vline(x, y1, y2, color=None, lw=0.35):
        pdf.set_draw_color(*(color or BORDER))
        pdf.set_line_width(lw)
        pdf.line(x, y1, x, y2)

    # ═══════════ تبدیل ساعت به «ساعت و دقیقه» ═══════════
    def hm_persian(hours):
        try:
            h = float(hours or 0)
        except Exception:
            return "۰ ساعت"
        if h <= 0:
            return "۰ ساعت"
        total_min = int(round(h * 60))
        hh = total_min // 60
        mm = total_min % 60
        if hh and mm:
            return f"{hh} ساعت و {mm} دقیقه"
        if hh:
            return f"{hh} ساعت"
        return f"{mm} دقیقه"

    # ═══════════ عدد به حروف ═══════════
    def num_to_words_fa(n):
        try:
            n = int(round(float(n)))
        except Exception:
            return "صفر"
        if n == 0:
            return "صفر"
        yekan = ['', 'یک', 'دو', 'سه', 'چهار', 'پنج', 'شش', 'هفت', 'هشت', 'نه']
        dahgan = ['', '', 'بیست', 'سی', 'چهل', 'پنجاه', 'شصت', 'هفتاد', 'هشتاد', 'نود']
        dah = ['ده', 'یازده', 'دوازده', 'سیزده', 'چهارده', 'پانزده',
               'شانزده', 'هفده', 'هجده', 'نوزده']
        sadgan = ['', 'صد', 'دویست', 'سیصد', 'چهارصد', 'پانصد',
                  'ششصد', 'هفتصد', 'هشتصد', 'نهصد']

        def three(x):
            p = []
            if x >= 100:
                p.append(sadgan[x // 100]); x %= 100
            if 10 <= x < 20:
                p.append(dah[x - 10])
            else:
                if x >= 20:
                    p.append(dahgan[x // 10])
                    if x % 10:
                        p.append(yekan[x % 10])
                elif x > 0:
                    p.append(yekan[x])
            return ' و '.join(q for q in p if q)

        scales = ['', ' هزار', ' میلیون', ' میلیارد', ' بیلیون']
        groups, i = [], 0
        while n > 0:
            g = n % 1000
            if g:
                groups.append(three(g) + scales[i])
            n //= 1000
            i += 1
        return ' و '.join(reversed(groups)) + ' ریال'

    # ═══════════════════════════════════════════════════════
    for item in slips:
        pay  = item.get('pay')     or {}
        emp  = item.get('emp')     or {}
        dept = item.get('dept')    or {}
        dets = item.get('details') or []
        if not emp or not pay:
            continue

        pdf.add_page()

        # قاب دوگانه دور برگه
        pdf.set_draw_color(*BORDER2)
        pdf.set_line_width(0.6)
        pdf.rect(6, 6, W - 12, 297 - 12, 'D')
        pdf.set_draw_color(*GOLD)
        pdf.set_line_width(0.25)
        pdf.rect(7.5, 7.5, W - 15, 297 - 15, 'D')

        y = M

        # ═══ ۱) سربرگ شرکت ═══
        hdr_h = 17
        pdf.set_fill_color(*NAVY)
        pdf.rect(M, y, CW, hdr_h, 'F')
        _draw_logo(pdf, company.get('logo') or '', M + 3, y + 3.5, 10, 10)
        put(M, y + 2, CW, hdr_h - 6,
            company.get('name') or APP_TITLE,
            align='C', size=F_TITLE, color=(255, 220, 130))
        info = []
        if company.get('phone'):
            info.append(f"تلفن: {company['phone']}")
        if company.get('address'):
            info.append(company['address'])
        if info:
            put(M, y + 10, CW, 4,
                '   •   '.join(info),
                align='C', size=F_TINY, color=(220, 228, 240))
        y += hdr_h
        pdf.set_fill_color(*GOLD)
        pdf.rect(M, y, CW, 0.8, 'F')
        y += 4.5

        # ═══ ۲) عنوان فیش ═══
        put(M, y, CW, 8, "فیش حقوق و دستمزد",
            align='C', size=F_TITLE - 1.5, color=NAVY)
        y += 9.5
        put(M, y, CW, 5,
            f"{MONTHS[int(pay['month']) - 1]}  سال  {pay['year']}",
            align='C', size=F_SUB, color=GOLD)
        y += 9

        # ═══ ۳) مشخصات پرسنل — 🆕 چیدمان RTL ═══
        col_w = CW / 3
        row_h = 8

        rows = [
            (f"نام: {emp.get('first_name','')} {emp.get('last_name','')}".strip(),
             f"وضعیت تاهل: {'متاهل' if emp.get('marital') else 'مجرد'}",
             f"شماره پرسنلی: {emp.get('personnel_code') or emp.get('id') or '-'}"),
            (f"کد ملی: {emp.get('national_code') or '-'}",
             f"محل خدمت: {(dept or {}).get('title') or '-'}",
             f"شماره حساب: {emp.get('account_number') or '-'}"),
            (f"شماره شناسنامه: {emp.get('id_number') or '-'}",
             f"عنوان شغلی: {emp.get('job_title') or '-'}",
             f"شماره بیمه: {emp.get('insurance_number') or '-'}"),
        ]

        for ri, row in enumerate(rows):
            x = M
            for text in reversed(row):                # 🆕 راست‌به‌چپ
                cell(x, y, col_w, row_h, text,
                     align='C', size=F_BODY, fill=SOFT_BG, lw=0.35)
                x += col_w
            y += row_h
        y += 3.5

        # ═══ ۴) جدول سه‌ستونه اصلی ═══
        w_work = 45
        w_ded  = 56
        w_pay  = CW - w_work - w_ded

        x_work = M + w_ded + w_pay   # راست‌ترین
        x_pay  = M + w_ded           # وسط
        x_ded  = M                   # چپ‌ترین

        head_h = 9
        pdf.set_fill_color(*NAVY)
        pdf.rect(M, y, CW, head_h, 'F')
        pdf.set_draw_color(*BORDER2)
        pdf.set_line_width(0.45)
        pdf.rect(M, y, CW, head_h, 'D')
        vline(x_work, y, y + head_h, color=GOLD, lw=0.5)
        vline(x_pay,  y, y + head_h, color=GOLD, lw=0.5)
        put(x_work, y, w_work, head_h, "اطلاعات کارکرد",
            align='C', size=F_HEAD, color=(255, 220, 130))
        put(x_pay,  y, w_pay,  head_h, "شرح پرداخت",
            align='C', size=F_HEAD, color=(255, 220, 130))
        put(x_ded,  y, w_ded,  head_h, "کسورات",
            align='C', size=F_HEAD, color=(255, 220, 130))
        y += head_h

        work_items = [
            ("کارکرد روزانه",   f"{pay.get('work_days') or 0:g} روز"),
            ("ساعت کارکرد",     hm_persian((pay.get('work_days') or 0) * 7.33)),
            ("اضافه‌کاری",      hm_persian(pay.get('overtime_hours') or 0)),
            ("جمعه‌کاری",       hm_persian(pay.get('friday_hours') or 0)),
            ("شب‌کاری",         hm_persian(pay.get('night_hours') or 0)),
            ("تعطیل‌کاری",      hm_persian(pay.get('holiday_hours') or 0)),
            ("مأموریت",         f"{pay.get('mission_days') or 0:g} روز"),
            ("کسر کار",         hm_persian(pay.get('absent_hours') or 0)),
        ]

        pay_items = [("حقوق پایه", pay.get('base_salary_monthly', 0))]
        pay_items += [(d['name'], d['amount']) for d in dets
                      if d.get('type') == 1 and (d.get('amount') or 0) > 0]
        for lbl, key in (("اضافه‌کاری",  'overtime_amount'),
                         ("شب‌کاری",     'night_amount'),
                         ("نوبت‌کاری",   'shift_amount'),
                         ("جمعه‌کاری",   'friday_amount'),
                         ("تعطیل‌کاری",  'holiday_amount'),
                         ("مأموریت",     'mission_amount')):
            v = pay.get(key) or 0
            if v:
                pay_items.append((lbl, v))

        def _is_loan_installment(name):
            n = (name or '').strip()
            return n.startswith('قسط وام') or n.startswith('قسط')

        ded_items = [(d['name'], d['amount']) for d in dets
                     if d.get('type') == 2
                     and (d.get('amount') or 0) > 0
                     and not _is_loan_installment(d.get('name'))]

        for li in (pay.get('loan_insts') or []):
            ded_items.append((f"قسط وام {li.get('installment_no','')}",
                              li.get('amount', 0)))
        if not (pay.get('loan_insts') or []) and (pay.get('loan_install') or 0) > 0:
            ded_items.append(("قسط وام", pay.get('loan_install')))

        max_len = max(len(work_items), len(pay_items), len(ded_items), 8)
        row_h = 7.5

        for i in range(max_len):
            bg = ROW_ALT if i % 2 == 0 else WHITE

            # ستون کارکرد (راست)
            pdf.set_fill_color(*bg)
            pdf.rect(x_work, y, w_work, row_h, 'F')
            pdf.set_draw_color(*BORDER)
            pdf.set_line_width(0.3)
            pdf.rect(x_work, y, w_work, row_h, 'D')
            if i < len(work_items):
                lbl, val = work_items[i]
                div_x = x_work + w_work * 0.44
                vline(div_x, y + 1.5, y + row_h - 1.5, color=(200, 210, 222), lw=0.25)
                put(div_x, y, w_work * 0.56 - PAD_X, row_h,
                    lbl, align='R', size=F_SMALL, color=NAVY_L)
                put(x_work + PAD_X, y, w_work * 0.44 - PAD_X, row_h,
                    val, align='C', size=F_BODY, color=BLUE)

            # ستون شرح پرداخت (وسط)
            pdf.set_fill_color(*bg)
            pdf.rect(x_pay, y, w_pay, row_h, 'F')
            pdf.set_draw_color(*BORDER)
            pdf.set_line_width(0.3)
            pdf.rect(x_pay, y, w_pay, row_h, 'D')
            if i < len(pay_items):
                lbl, val = pay_items[i]
                div_x = x_pay + w_pay * 0.34
                vline(div_x, y + 1.5, y + row_h - 1.5, color=(200, 210, 222), lw=0.25)
                put(div_x, y, w_pay * 0.66 - PAD_X, row_h,
                    lbl, align='R', size=F_BODY, color=NAVY_L)
                put(x_pay + PAD_X, y, w_pay * 0.34 - PAD_X, row_h,
                    fmt(val), align='C', size=F_BODY, color=TXT)

            # ستون کسورات (چپ)
            pdf.set_fill_color(*bg)
            pdf.rect(x_ded, y, w_ded, row_h, 'F')
            pdf.set_draw_color(*BORDER)
            pdf.set_line_width(0.3)
            pdf.rect(x_ded, y, w_ded, row_h, 'D')
            if i < len(ded_items):
                lbl, val = ded_items[i]
                div_x = x_ded + w_ded * 0.48
                vline(div_x, y + 1.5, y + row_h - 1.5, color=(200, 210, 222), lw=0.25)
                put(div_x, y, w_ded * 0.52 - PAD_X, row_h,
                    lbl, align='R', size=F_BODY, color=NAVY_L)
                put(x_ded + PAD_X, y, w_ded * 0.48 - PAD_X, row_h,
                    fmt(val), align='C', size=F_BODY, color=RED)

            y += row_h

        # ═══ ۵) ردیف جمع‌ها ═══
        total_ded  = (pay.get('gross_salary') or 0) - (pay.get('net_salary') or 0)
        total_earn = pay.get('gross_salary', 0) or 0

        sum_h = 9
        pdf.set_fill_color(*ROW_HD)
        pdf.rect(M, y, CW, sum_h, 'F')
        pdf.set_draw_color(*BORDER2)
        pdf.set_line_width(0.5)
        pdf.rect(M, y, CW, sum_h, 'D')
        vline(x_work, y, y + sum_h, color=BORDER2, lw=0.4)
        vline(x_pay,  y, y + sum_h, color=BORDER2, lw=0.4)
        put(x_work, y, w_work, sum_h, "جمع کارکرد",
            align='C', size=F_SMALL, color=NAVY)
        put(x_pay,  y, w_pay,  sum_h,
            f"جمع کل پرداختی:   {fmt(total_earn)}",
            align='C', size=F_HEAD, color=NAVY)
        put(x_ded,  y, w_ded,  sum_h,
            f"جمع کسورات:   {fmt(total_ded)}",
            align='C', size=F_HEAD, color=RED)
        y += sum_h + 3

        # ═══ ۶) نوار خالص پرداختی ═══
        net_h = 12
        pdf.set_fill_color(*GOLD_BG)
        pdf.rect(M, y, CW, net_h, 'F')
        pdf.set_draw_color(*GOLD)
        pdf.set_line_width(0.55)
        pdf.rect(M, y, CW, net_h, 'D')
        put(M, y, CW, net_h,
            f"خالص پرداختی:       {fmt(pay.get('net_salary', 0))}       ریال",
            align='C', size=F_NET, color=GREEN)
        y += net_h + 3.5

        # ═══ ۷) مبلغ به حروف ═══
        words = num_to_words_fa(pay.get('net_salary', 0))
        words_h = 8
        cell(M, y, CW, words_h, "", fill=(252, 252, 254), border=1, lw=0.35)
        put(M + 3, y, CW - 6, words_h,
            f"آقای/خانم {emp.get('first_name','')} {emp.get('last_name','')} "
            f"مبلغ {words} به حساب شما واریز گردید.",
            align='R', size=F_SMALL, color=PURPLE)
        y += words_h + 2

        # ═══ ۸) وضعیت پرداخت + بیمه کارفرما ═══
        paid = pay.get('payment_status') == 'paid'
        status = "پرداخت شده" if paid else "در انتظار پرداخت"
        if paid and pay.get('payment_date'):
            status += f"   —   تاریخ پرداخت: {pay.get('payment_date')}"

        stat_h = 7.5
        cell(M, y, CW, stat_h, "", fill=WHITE, border=1, lw=0.3)
        put(M + 3, y, CW - 6, stat_h,
            f"وضعیت پرداخت: {status}",
            align='R', size=F_SMALL, color=GREEN if paid else RED)
        y += stat_h

        if pay.get('insurance_er'):
            cell(M, y, CW, stat_h, "", fill=WHITE, border=1, lw=0.3)
            put(M + 3, y, CW - 6, stat_h,
                f"سهم بیمه کارفرما (اطلاعاتی): {fmt(pay.get('insurance_er'))} ریال",
                align='R', size=F_SMALL, color=ORANGE)
            y += stat_h

        # ═══ ۹) سه کادر امضا ═══
        y += 10
        sig_y = max(y, 248)
        if sig_y + 28 > 285:
            sig_y = 250

        gap   = 4
        box_w = (CW - 2 * gap) / 3
        box_h = 27

        boxes = [
            (M + 2 * (box_w + gap), "امضای کارفرما",
             company.get('sign_manager') or '.....................', GOLD),
            (M + box_w + gap,       "مهر شرکت",
             "....................."                          , NAVY_L),
            (M,                     "امضای کارگر",
             f"{emp.get('first_name','')} {emp.get('last_name','')}".strip() or '...............', PURPLE),
        ]

        for bx, title, name, accent in boxes:
            pdf.set_fill_color(*SOFT_BG)
            pdf.rect(bx, sig_y, box_w, box_h, 'F')
            pdf.set_draw_color(*accent)
            pdf.set_line_width(0.45)
            pdf.rect(bx, sig_y, box_w, box_h, 'D')
            put(bx, sig_y + 2, box_w, 5, title,
                align='C', size=F_SMALL, color=accent)
            pdf.set_draw_color(*GOLD)
            pdf.set_line_width(0.25)
            pdf.line(bx + 5, sig_y + 10, bx + box_w - 5, sig_y + 10)
            put(bx, sig_y + box_h - 8, box_w, 5, name,
                align='C', size=F_TINY, color=MUTED)

        # ═══ ۱۰) پانویس ═══
        put(M, 289, CW, 4,
            f"صادر شده با {APP_TITLE}   •   {DEVELOPER}   •   {DEVELOPER_PHONE}",
            align='C', size=F_TINY, color=MUTED)

    pdf.output(path)
    return path



def _sync_annual_rates(db, cid, table, values, rid=None):
    """Keep parallel legacy tables and the annual settings row coherent after edits."""
    v = dict(values or {})
    year = v.get('year')
    if year in (None, ''):
        return
    try:
        year = int(year)
    except (ValueError, TypeError):
        return
    rate_keys = {
        'حق مسکن': 'housing_allowance',
        'بن کارگری': 'food_allowance',
        'حق تاهل': 'marriage_allowance',
        'حق اولاد': 'child_allowance',
    }
    if table == 'rate_years':
        for title, key in rate_keys.items():
            if v.get(key) is None:
                continue
            rows = db.q('SELECT id FROM benefits WHERE company_id=? AND year=? AND title=? ORDER BY id',
                        (cid, year, title))
            if rows:
                db.update('benefits', rows[-1]['id'], {'amount': int(v[key])})
            else:
                calc_type = {'حق مسکن': 'fixed', 'بن کارگری': 'fixed', 'حق تاهل': 'marital', 'حق اولاد': 'child'}[title]
                taxable, insurable = (1, 0) if title == 'حق اولاد' else (1, 1)
                db.insert('benefits', dict(company_id=cid, year=year, title=title, amount=int(v[key]),
                                          taxable=taxable, insurable=insurable, monthly=1, calc_type=calc_type,
                                          severance_basis=0))
        # Keep the standard wide bracket as fallback without overwriting specific seniority rules.
        by = v.get('base_year_daily')
        if by is not None:
            broad = db.q1('SELECT id FROM base_year_rules WHERE company_id=? AND year=? AND min_service<=1 AND max_service>=20 ORDER BY id LIMIT 1',
                          (cid, year))
            if broad:
                db.update('base_year_rules', broad['id'], {'amount': int(by)})
            else:
                db.insert('base_year_rules', dict(company_id=cid, year=year, min_service=1, max_service=20, amount=int(by)))
        # Single annual Eid rule mirrors minimum wage and legal entitlement parameters.
        if v.get('min_daily_wage') is not None:
            er = db.q1('SELECT id FROM eid_rules WHERE company_id=? AND year=? ORDER BY id LIMIT 1', (cid, year))
            eid_data = {'daily_min_wage': int(v.get('min_daily_wage') or 0),
                        'min_days': int(v.get('eid_min_days') or 60),
                        'max_days': int(v.get('eid_max_days') or 90)}
            if er:
                db.update('eid_rules', er['id'], eid_data)
            else:
                db.insert('eid_rules', dict(company_id=cid, year=year, **eid_data))
    elif table == 'benefits' and v.get('title') in rate_keys and v.get('amount') is not None:
        key = rate_keys[v['title']]
        db.x(f'UPDATE rate_years SET "{key}"=? WHERE company_id=? AND year=?', (int(v['amount']), cid, year))
    elif table == 'eid_rules':
        values_to_set = {}
        if v.get('daily_min_wage') is not None: values_to_set['min_daily_wage'] = int(v['daily_min_wage'])
        if v.get('min_days') is not None: values_to_set['eid_min_days'] = int(v['min_days'])
        if v.get('max_days') is not None: values_to_set['eid_max_days'] = int(v['max_days'])
        if values_to_set:
            rows = db.q1('SELECT id FROM rate_years WHERE company_id=? AND year=? ORDER BY id LIMIT 1', (cid, year))
            if rows: db.update('rate_years', rows['id'], values_to_set)
    elif table == 'base_year_rules':
        if int(v.get('min_service') or 1) <= 1 and int(v.get('max_service') or 0) >= 20 and v.get('amount') is not None:
            rows = db.q1('SELECT id FROM rate_years WHERE company_id=? AND year=? ORDER BY id LIMIT 1', (cid, year))
            if rows: db.update('rate_years', rows['id'], {'base_year_daily': int(v['amount'])})


def _set_payroll_payment(db, payroll_id, paid, company_id=None):
    """ثبت/لغو پرداخت فیش + به‌روزرسانی دقیق وضعیت اقساط، پاداش، کسورات."""
    target = 'paid' if paid else 'unpaid'
    with db.tx() as conn:
        p = conn.execute('SELECT * FROM payrolls WHERE id=?', (payroll_id,)).fetchone()
        if not p:
            return 'فیش حقوقی پیدا نشد.'
        if company_id is not None and p['company_id'] != company_id:
            return 'این فیش متعلق به شرکت فعال نیست.'
        if (p['payment_status'] or 'unpaid') == target:
            return None

        if paid:
            # ═══ تأیید اقساط محاسبه‌شده ═══
            insts = conn.execute("""SELECT * FROM loan_installments
                WHERE calculated_payroll_id=? AND status='calculated'""",
                (payroll_id,)).fetchall()
            expected = rnd(p['loan_install'] or 0)
            actual = sum(rnd(x['amount'] or 0) for x in insts)
            if expected > 0 and actual != expected:
                return (f'اقساط محاسبه‌شده ({fmt(actual)}) با مبلغ فیش ({fmt(expected)}) '
                        f'مطابقت ندارد؛ ابتدا فیش را بازمحاسبه کنید.')

            for x in insts:
                amt = rnd(x['amount'] or 0)
                conn.execute("""UPDATE loan_installments
                    SET status='paid', is_paid=1,
                        paid_payroll_id=?, paid_year=?, paid_month=?
                    WHERE id=?""",
                    (payroll_id, p['year'], p['month'], x['id']))
                conn.execute("""UPDATE loans
                    SET remaining_balance=MAX(COALESCE(remaining_balance,0)-?,0)
                    WHERE id=?""", (amt, x['loan_id']))
                left = conn.execute("""SELECT COUNT(*) FROM loan_installments
                    WHERE loan_id=? AND status<>'paid' AND status<>'waived'""",
                    (x['loan_id'],)).fetchone()[0]
                if left == 0:
                    conn.execute("UPDATE loans SET status=1, remaining_balance=0 WHERE id=?",
                                 (x['loan_id'],))

            # 🆕 علامت‌گذاری پاداش‌های این فیش به‌عنوان پرداخت‌شده
            conn.execute("""UPDATE bonuses
                SET payment_status='paid', paid_year=?, paid_month=?
                WHERE paid_payroll_id=? AND payment_status='calculated'""",
                (p['year'], p['month'], payroll_id))

            # 🆕 کسورات اعمال‌شده در این فیش به applied نهایی می‌رسند
            conn.execute("""UPDATE deductions
                SET payment_status='applied'
                WHERE applied_payroll_id=? AND payment_status='pending'""",
                (payroll_id,))

            conn.execute("UPDATE payrolls SET payment_status='paid', payment_date=? WHERE id=?",
                         (jalali_today_str(), payroll_id))

        else:
            # ═══ لغو پرداخت ═══
            insts = conn.execute("""SELECT * FROM loan_installments
                WHERE paid_payroll_id=? AND status='paid'""", (payroll_id,)).fetchall()
            for x in insts:
                amt = rnd(x['amount'] or 0)
                conn.execute("""UPDATE loan_installments
                    SET status='calculated', is_paid=0,
                        paid_payroll_id=NULL, paid_year=NULL, paid_month=NULL
                    WHERE id=?""", (x['id'],))
                principal = conn.execute("SELECT principal FROM loans WHERE id=?",
                                         (x['loan_id'],)).fetchone()
                cap = rnd((principal['principal'] if principal else 0) or 0)
                conn.execute("""UPDATE loans
                    SET remaining_balance=MIN(?, COALESCE(remaining_balance,0)+?), status=0
                    WHERE id=?""", (cap, amt, x['loan_id']))

            # 🆕 برگرداندن پاداش‌ها به calculated
            conn.execute("""UPDATE bonuses
                SET payment_status='calculated', paid_year=NULL, paid_month=NULL
                WHERE paid_payroll_id=? AND payment_status='paid'""",
                (payroll_id,))

            conn.execute("UPDATE payrolls SET payment_status='unpaid', payment_date=NULL WHERE id=?",
                         (payroll_id,))
    return None


# تقویت پرداخت دوره‌ای به‌صورت تکی و گروهی در صفحه حقوق و دستمزد.
_V_PAYROLL_ORIGINAL = App.v_payroll

def _app_v_payroll(self):
    view = _V_PAYROLL_ORIGINAL(self)

    def mark_all_paid(value):
        rows = self.db.q('SELECT id FROM payrolls WHERE company_id=? AND year=? AND month=? ORDER BY emp_id',
                         (self.cid, self.year, self.month))
        changed = 0
        for row in rows:
            message = _set_payroll_payment(self.db, row['id'], value, self.cid)
            if message:
                self.info('مدیریت پرداخت گروهی',
                          f'{changed} فیش تغییر کرد. مورد بعدی متوقف شد:\n{message}')
                self.refresh(); return
            changed += 1
        self.toast(f'وضعیت پرداخت {changed} فیش به‌روزرسانی شد')
        self.refresh()

    def mini(text, handler, color, icon):
        return ft.Container(
            content=ft.Row([
                ft.Icon(icon, color=color, size=14),
                txt(text, 10, True, color),
            ], spacing=3, tight=True),
            padding=pad_sym(8, 4), border_radius=8, ink=True,
            on_click=handler,
            border=border_all(1, alpha(color, 0x55)),
            bgcolor=alpha(color, 0x12))

    panel = ft.Container(
        content=ft.Row([
            txt("پرداخت گروهی:", 10, color=T()['muted']),
            mini("پرداخت همه",
                 lambda e: self.confirm('همه فیش‌های این دوره پرداخت‌شده شوند؟',
                                        lambda: mark_all_paid(True), 'ثبت پرداخت گروهی', False),
                 T()['success'], _ic('CHECK_CIRCLE')),
            mini("لغو همه",
                 lambda e: self.confirm('وضعیت پرداخت همه بازگردانده شود؟',
                                        lambda: mark_all_paid(False), 'بازگردانی', False),
                 T()['danger'], _ic('UNDO')),
            ft.Container(expand=True),
        ], spacing=6),
        padding=pad_sym(8, 4))

    try:
        controls = list(view.controls)
        idx = min(1, len(controls))
        controls.insert(idx, panel)
        view.controls = controls
    except Exception:
        pass
    return view


# ═══════════════════════ اندروید: باز کردن / اشتراک‌گذاری / اسکرین‌شات ═══════════════════════
def _is_android():
    return bool(os.environ.get("ANDROID_ROOT") or os.environ.get("ANDROID_DATA")
                or os.environ.get("ANDROID_ARGUMENT"))

_FILE_REG = {}
_FILE_SRV = {'srv': None, 'port': 0}
_SERVICES = {}


class _FileHandler(http.server.BaseHTTPRequestHandler):
    """سرویس‌دهی فقط فایل‌های ثبت‌شده، فقط روی همین گوشی (127.0.0.1)."""
    def log_message(self, *a): pass

    def do_GET(self):
        try:
            parts = urllib.parse.unquote(self.path.split('?')[0]).split('/')
            token = parts[2] if len(parts) > 2 else ''
            p = _FILE_REG.get(token)
            if not p or not os.path.isfile(p):
                self.send_error(404); return
            ctype = mimetypes.guess_type(p)[0] or 'application/octet-stream'
            disp = 'inline' if ctype.startswith('image/') else 'attachment'
            self.send_response(200)
            self.send_header('Content-Type', ctype)
            self.send_header('Content-Length', str(os.path.getsize(p)))
            self.send_header('Content-Disposition',
                             disp + "; filename*=UTF-8''" + urllib.parse.quote(os.path.basename(p)))
            self.end_headers()
            with open(p, 'rb') as f:
                shutil.copyfileobj(f, self.wfile)
        except Exception:
            pass


def _file_url(path):
    if _FILE_SRV['srv'] is None:
        srv = http.server.ThreadingHTTPServer(('127.0.0.1', 0), _FileHandler)
        srv.daemon_threads = True
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        _FILE_SRV['srv'] = srv
        _FILE_SRV['port'] = srv.server_address[1]
    token = secrets.token_urlsafe(8)
    _FILE_REG[token] = path
    return f"http://127.0.0.1:{_FILE_SRV['port']}/f/{token}/{urllib.parse.quote(os.path.basename(path))}"


async def _await_if(r):
    if inspect.isawaitable(r):
        return await r
    return r


def _page_service(page, cls_name):
    key = (id(page), cls_name)
    if key in _SERVICES:
        return _SERVICES[key]
    cls = getattr(ft, cls_name, None)
    if cls is None:
        return None
    svc = cls()
    try:
        services = getattr(page, 'services', None)
        if services is not None and svc not in services:
            services.append(svc)
    except Exception:
        pass
    _SERVICES[key] = svc
    return svc


async def _launch_url(page, url):
    try:
        svc = _page_service(page, 'UrlLauncher')
        if svc is not None:
            await _await_if(svc.launch_url(url)); return True
    except Exception:
        log_error(traceback.format_exc())
    try:
        await _await_if(page.launch_url(url)); return True
    except Exception:
        log_error(traceback.format_exc())
    return False


async def open_document(page, path):
    """باز کردن فایل: دسکتاپ مستقیم، اندروید از طریق مرورگر/نمایشگر سیستم."""
    if getattr(page, 'web', False):
        return False
    if not _is_android() and open_file(path):
        return True
    try:
        url = _file_url(path)
    except Exception:
        log_error(traceback.format_exc()); return False
    if await _launch_url(page, url):
        return True
    return await _launch_url(page, 'file://' + path)


async def share_document(page, path, label=''):
    """'shared' | 'saved' (در دانلودها ذخیره شد) | '' (ناموفق)"""
    Share = getattr(ft, 'Share', None)
    SF = getattr(ft, 'ShareFile', None)
    if Share is not None and SF is not None:
        try:
            svc = _page_service(page, 'Share')
            maker = getattr(SF, 'from_path', None)
            f = maker(path) if maker else SF(path=path)
            await _await_if(svc.share_files([f], title=label or None, text=label or None))
            return 'shared'
        except Exception:
            log_error(traceback.format_exc())
    if await open_document(page, path):
        return 'saved'
    return ''


async def _copy_text(page, s):
    try:
        f = getattr(page, 'set_clipboard', None)
        if callable(f):
            await _await_if(f(s)); return True
        await _await_if(ft.Clipboard().set(s)); return True
    except Exception:
        return False


def _app_file_dialog(self, path, title='فایل آماده است', count=None):
    label = f'{title} ({count} فیش)' if count else title

    async def do_open(ev):
        if not await open_document(self.page, path):
            self.toast('باز کردن مستقیم ممکن نشد. از «اشتراک‌گذاری» یا مسیر فایل استفاده کنید.', True)

    async def do_share(ev):
        r = await share_document(self.page, path, label)
        if r == 'saved':
            self.toast('فایل در پوشه دانلودها ذخیره شد؛ از همان‌جا می‌توانید ارسال کنید.')
        elif not r:
            self.toast('اشتراک‌گذاری ممکن نشد؛ فایل در مسیر نمایش‌داده‌شده ذخیره شده است.', True)

    async def do_copy(ev):
        self.toast('مسیر کپی شد' if await _copy_text(self.page, path) else 'کپی ممکن نشد',
                   False)

    d = ft.AlertDialog(
        modal=True, title=ft.Text(label, size=13),
        content=ft.Container(ft.Column([
            txt('فایل ساخته و ذخیره شد.', 11, True),
            ft.Row([gbtn('📤 اشتراک‌گذاری', _ic('SHARE'), do_share, T()['primary']),
                    gbtn('📂 باز کردن', _ic('OPEN_IN_NEW'), do_open, T()['success'])],
                   spacing=6, wrap=True, run_spacing=6),
            txt('محل ذخیره:', 10, color=T()['muted']),
            ft.Container(txt(path, 10, selectable=True), bgcolor=T()['bg'],
                         padding=8, border_radius=8),
            tbtn('📋 کپی مسیر', do_copy),
        ], spacing=8, tight=True, scroll=ft.ScrollMode.AUTO),
            width=min((self.page.width or 400) - 32, 400)),
        actions=[tbtn('بستن', lambda e: self.close_dlg(d))])
    self.open_dlg(d)


def _app_shot_wrap(self, content):
    Scr = getattr(ft, 'Screenshot', None)
    if Scr is None:
        return content, None
    try:
        shot = K(Scr, content=content)
        return shot, shot
    except Exception:
        return content, None


async def _app_capture_shot(self, shot, name):
    """اسکرین‌شات تومارِ کامل محتوا (حتی بخش‌های خارج از صفحه) و ذخیره به‌صورت PNG."""
    if shot is None:
        self.toast('گرفتن اسکرین‌شات در این دستگاه پشتیبانی نمی‌شود.', True); return
    try:
        fn = getattr(shot, 'capture_async', None) or getattr(shot, 'capture', None)
        data = None
        for ratio in (2.5, 1.5, 1.0):
            try:
                data = await _await_if(fn(pixel_ratio=ratio))
            except TypeError:
                data = await _await_if(fn())
            except Exception:
                data = None
            if data:
                break
        if not data:
            self.toast('اسکرین‌شات ساخته نشد؛ دوباره تلاش کنید.', True); return
        if isinstance(data, str):
            data = base64.b64decode(data)
        path = os.path.join(export_dir(), f"{name}_{datetime.now():%Y%m%d_%H%M%S}.png")
        with open(path, 'wb') as f:
            f.write(bytes(data))
        self.file_dialog(path, '📸 اسکرین‌شات کامل ذخیره شد')
    except Exception:
        log_error(traceback.format_exc())
        self.toast('خطا در گرفتن اسکرین‌شات', True)


def _app_swipe_wrap(self, content):
    """کشیدن انگشت بین تب‌ها غیرفعال است — محتوا بدون پوشش برمی‌گردد."""
    return content


def _app_debounce(self, key, fn, delay=0.25):
    timers = self.__dict__.setdefault('_timers', {})
    old = timers.get(key)
    if old: old.cancel()
    def run():
        try: fn()
        except Exception: log_error(traceback.format_exc())
    t = threading.Timer(delay, run); t.daemon = True
    timers[key] = t; t.start()


def _app_on_page_resize(self, e=None):
    try:
        w = self.page.width or 0
        if self.body is not None:
            side = max(8, int((w - 840) / 2)) if w > 900 else 8
            self.body.padding = pad_sym(side, 6)
            self.body.update()
    except Exception:
        pass
    h = getattr(self, '_view_resize', None)
    if h:
        try: h()
        except Exception: pass


App.file_dialog = _app_file_dialog
App.shot_wrap = _app_shot_wrap
App.capture_shot = _app_capture_shot
App._swipe_wrap = _app_swipe_wrap
App.debounce = _app_debounce
App._on_page_resize = _app_on_page_resize
App._view_resize = None


# ═══════════════════════ اشتراک نسخه وب در شبکه محلی ═══════════════════════
WEB = {'proc': None, 'thread': None, 'port': 8550, 'blocked': False, 'mode': ''}


def _lan_ips():
    if _is_android():
        # روی اندروید معمولاً IP داخلی قابل استفاده در شبکه نیست
        return []
    ips = []
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(('10.255.255.255', 1))
        ips.append(s.getsockname()[0])
        s.close()
    except Exception:
        pass
    try:
        for r in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ip = r[4][0]
            if ip not in ips and not ip.startswith('127.'):
                ips.append(ip)
    except Exception:
        pass
    return ips


def _port_open(port, host='127.0.0.1', timeout=0.4):
    try:
        with socket.create_connection((host, int(port)), timeout=timeout):
            return True
    except Exception:
        return False


def _run_flet_web(port):
    """اجرای سرور وب — سازگار با دسکتاپ و اندروید."""
    # روی اندروید، مسیر پیش‌فرض Flet برای وب منطقی نیست
    if _is_android():
        try:
            fn = getattr(ft, 'run', None) or getattr(ft, 'app', None)
            if not callable(fn):
                raise RuntimeError('تابع اجرای Flet پیدا نشد.')
            ps = _params(fn)
            kw = {}
            if 'host' in ps: kw['host'] = '0.0.0.0'
            if 'port' in ps: kw['port'] = int(port)
            if 'name' in ps: kw['name'] = APP_TITLE
            AV = getattr(ft, 'AppView', None)
            web_view = getattr(AV, 'WEB_BROWSER', None) if AV is not None else None
            if 'view' in ps and web_view is not None: kw['view'] = web_view
            if 'target' in ps:
                kw['target'] = main
                fn(**kw)
            else:
                fn(main, **kw)
            return
        except Exception as e:
            log_error(f'Android web run failed: {e}')
            raise

    # ─── دسکتاپ: همان کد قبلی ───
    for key in ('FLET_SERVER_IP', 'FLET_SERVER_HOST'):
        os.environ[key] = '0.0.0.0'
    # ...
    for key in ('FLET_SERVER_PORT', 'FLET_PORT', 'PORT'):
        os.environ[key] = str(int(port))
        # ⚠️ این دو خط حذف شدند چون باعث باگ WebSocket در Flet 1.0 می‌شوند
    view_val = None
    try:
        AV = getattr(ft, 'AppView', None)
        if AV is not None and hasattr(AV, 'WEB_BROWSER'):
            view_val = AV.WEB_BROWSER
    except Exception:
        pass

    fn = getattr(ft, 'run', None) or getattr(ft, 'app', None)
    if not callable(fn):
        raise RuntimeError('تابع اجرای Flet پیدا نشد.')

    try:
        ps = _params(fn)
    except Exception:
        ps = {}

    kw = {}
    if 'host' in ps: kw['host'] = '0.0.0.0'
    if 'port' in ps: kw['port'] = int(port)
    if 'name' in ps: kw['name'] = APP_TITLE
    if view_val is not None and 'view' in ps: kw['view'] = view_val
    if 'target' in ps:  # سبک قدیمی
        kw['target'] = main
        fn(**kw)
    else:
        fn(main, **kw)

def _thread_web(port):
    try: _run_flet_web(port)
    except BaseException: log_error(traceback.format_exc())


def web_share_active():
    p = WEB['proc']; t = WEB['thread']
    return bool((p and p.poll() is None) or (t and t.is_alive() and not WEB['blocked']))


def web_share_start(port):
    try:
        port = int(port)
    except Exception:
        return False, 'شماره پورت معتبر نیست.'
    if not 1024 <= port <= 65535:
        return False, 'پورت باید بین ۱۰۲۴ تا ۶۵۵۳۵ باشد.'

    # ⬇⬇⬇ این بلوک جدید را اضافه کن ⬇⬇⬇
    if _is_android():
        # روی اندروید، subprocess و flet CLI وجود ندارند.
        # فقط thread داخلی می‌تواند کار کند و فقط از خود گوشی قابل دسترسی است.
        if web_share_active():
            return True, ''
        try:
            th = threading.Thread(target=_thread_web, args=(port,), daemon=True)
            th.start()
            WEB['thread'] = th
            WEB['mode'] = 'thread'
            for _ in range(60):
                if _port_open(port):
                    WEB['port'] = port
                    WEB['blocked'] = False
                    return True, ''
                if not th.is_alive():
                    break
                time.sleep(0.25)
            return False, (
                'روی اندروید، اشتراک در شبکه محدود است.\n\n'
                'روی خود همین گوشی، این آدرس را در مرورگر باز کنید:\n'
                f'  http://127.0.0.1:{port}/\n\n'
                'برای اشتراک بین چند گوشی، بهتر است APK را روی هر گوشی '
                'به‌صورت جداگانه نصب کنید (دیتابیس هر گوشی مستقل است).'
            )
        except Exception as e:
            log_error(traceback.format_exc())
            return False, f'اجرای سرویس وب روی اندروید ممکن نشد: {e}'
    # ⬆⬆⬆ پایان بلوک ⬆⬆⬆

    if web_share_active():
        return True, ''
    # ... بقیه تابع برای دسکتاپ دست‌نخورده ...

    if _port_open(port):
        return False, (
            f'پورت {port} اشغال است. اگر Flet قبلاً روی این پورت اجرا شده، '
            f'آن را ببندید یا پورت دیگری (مثل {port + 1}) امتحان کنید.'
        )

    me = os.path.abspath(__file__) if '__file__' in globals() else ''
    if not me or not os.path.isfile(me):
        return False, 'مسیر فایل main.py پیدا نشد.'

    env = dict(os.environ)
    # ⚠️ FLET_FORCE_WEB_SERVER را حذف کردیم چون در Flet 1.0 باگ WebSocket ایجاد می‌کند
    env.pop('FLET_FORCE_WEB_SERVER', None)
    env.pop('FLET_WEB_RENDERER', None)
    env['FLET_SERVER_IP'] = '0.0.0.0'
    env['FLET_SERVER_PORT'] = str(port)

    # دستورات مختلفی که ممکن است روی این سیستم جواب بدهند
    candidates = [
        # ۱. python -m flet run --web (پایدارترین روش)
        [sys.executable, '-m', 'flet', 'run', '--web',
         '--host', '0.0.0.0', '--port', str(port), me],
        # ۲. flet روی PATH
        ['flet', 'run', '--web',
         '--host', '0.0.0.0', '--port', str(port), me],
        # ۳. اجرای مستقیم main.py با --web-share (fallback)
        [sys.executable, me, '--web-share', str(port)],
    ]

    for cmd in candidates:
        # اگر دستور «flet» است ولی روی PATH نیست، رد کن
        if cmd[0] == 'flet':
            if shutil.which('flet') is None:
                continue

        try:
            proc = subprocess.Popen(
                cmd,
                env=env,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                cwd=os.path.dirname(me) or None,
            )
        except FileNotFoundError:
            continue
        except Exception as e:
            log_error(f'Popen failed for {cmd[0]} {cmd[1]}: {e}')
            continue

        # تا ۲۰ ثانیه صبر کن تا پورت باز شود
        ok = False
        for _ in range(80):
            if _port_open(port):
                ok = True
                break
            if proc.poll() is not None:
                # پروسه مرده — لاگش را بخوان
                try:
                    out = proc.stdout.read().decode('utf-8', 'ignore')[:500]
                    log_error(f'flet subprocess died: {out}')
                except Exception:
                    pass
                break
            time.sleep(0.25)

        if ok:
            WEB['proc'] = proc
            WEB['mode'] = 'proc'
            WEB['port'] = port
            WEB['blocked'] = False
            return True, ''

        # پاکسازی و امتحان بعدی
        try:
            proc.terminate()
            proc.wait(timeout=2)
        except Exception:
            try:
                proc.kill()
            except Exception:
                pass

    return False, (
        'سرویس وب بالا نیامد.\n\n'
        'دستور زیر را در ترمینال خودتان اجرا کنید:\n'
        f'  flet run --web --host 0.0.0.0 --port {port} main.py\n\n'
        'سپس در مرورگر این آدرس را باز کنید:\n'
        f'  http://127.0.0.1:{port}/\n\n'
        'و از گوشی دیگر (روی همان وای‌فای):\n'
        f'  http://IP-رایانه:{port}/'
    )


def web_share_stop():
    p = WEB['proc']
    if p is not None:
        try:
            p.terminate(); p.wait(timeout=4)
        except Exception:
            try: p.kill()
            except Exception: pass
        WEB['proc'] = None
    if WEB['thread'] is not None:
        WEB['blocked'] = True  # ورود جدید از وب مسدود می‌شود


def _app_v_webshare(self):
    page_is_web = bool(getattr(self.page, 'web', False))
    port_f = tf('پورت', WEB['port'], kb=True, width=110)
    status = txt('', 11, True)
    info = ft.Column(spacing=6)

    def refresh_info():
        info.controls.clear()
        if web_share_active():
            status.value = '🟢 فعال — دیگران با آدرس‌های زیر وارد شوند'; status.color = T()['success']
            ips = _lan_ips() or ['IP-دستگاه']
            for ip in ips:
                url = f"http://{ip}:{WEB['port']}"
                async def cp(ev, u=url):
                    self.toast('آدرس کپی شد' if await _copy_text(self.page, u) else 'کپی ممکن نشد')
                info.controls.append(card(ft.Row([
                    txt(url, 13, True, T()['primary'], expand=True, selectable=True),
                    iconbtn(_ic('CONTENT_COPY'), cp, T()['accent'], 18, 'کپی آدرس')]), padding=8))
        else:
            status.value = '⚪ غیرفعال'; status.color = T()['muted']
        try: info.update(); status.update()
        except Exception: pass

    def on_toggle(e):
        if e.control.value:
            ok, msg = web_share_start(port_f.value)
            if not ok:
                e.control.value = False
                try: e.control.update()
                except Exception: pass
                self.toast(msg, True)
        else:
            web_share_stop()
            self.toast('اشتراک‌گذاری وب غیرفعال شد')
        refresh_info()

    sw = K(ft.Switch, label='فعال‌سازی لوکال‌هاست (اشتراک در شبکه)', value=web_share_active(),
           active_color=T()['accent'], on_change=on_toggle)
    refresh_info()
    notes = ['• گوشی/رایانه‌های دیگر باید به همین وای‌فای (شبکه) وصل باشند.',
             '• دیگران آدرس را در مرورگر خود باز می‌کنند و با رمز برنامه وارد می‌شوند.',
             '• اطلاعات همین دیتابیس مشترک است؛ فقط به افراد مورد اعتماد آدرس بدهید.',
             '• با خاموش‌کردن کلید، دسترسی دیگران قطع می‌شود.']
    if page_is_web:
        notes.insert(0, '⚠️ شما همین‌الان از نسخه وب استفاده می‌کنید؛ آدرسی که باز کرده‌اید همان آدرس اشتراک است.')
    return ft.ListView([
        card(ft.Column([txt('🌐 اشتراک نسخه وب برنامه', 13, True), sw, port_f, status], spacing=8), padding=12),
        info,
        card(ft.Column([txt(n, 10, color=T()['muted']) for n in notes], spacing=4), padding=10),
    ], spacing=8, expand=True, padding=pad_only(bottom=20))

App.v_webshare = _app_v_webshare


# ═══════════════════════ مدیریت قالب قرارداد ═══════════════════════
CONTRACT_MARKERS_FA = (
    ("عنوان اصلی", "#T عنوان سند\n"), ("سرتیتر بخش", "#S عنوان بخش\n"),
    ("عنوان ماده", "#A ماده ۱ — عنوان\n"), ("پاراگراف", "#P متن پاراگراف\n"),
    ("وسط‌چین", "#C متن وسط‌چین\n"), ("راست‌چین", "#R متن راست‌چین\n"),
    ("چپ‌چین", "#L متن چپ‌چین\n"), ("کادر برجسته", "#BOX متن کادر\n"),
    ("خط جداکننده", "#HR\n"),
    ("جدول", "#TBL\nعنوان|مقدار|عنوان|مقدار\n#/TBL\n"),
)


def _insert_snippet(editor, snippet):
    v = editor.value or ''
    pos = len(v)
    sel = getattr(editor, 'selection', None)
    try:
        if sel is not None:
            a = getattr(sel, 'start', None)
            if a is None:
                a = min(getattr(sel, 'base_offset', pos), getattr(sel, 'extend_offset', pos))
            if a is not None and 0 <= a <= len(v): pos = int(a)
    except Exception:
        pos = len(v)
    editor.value = v[:pos] + snippet + v[pos:]
    try:
        TS = getattr(ft, 'TextSelection', None)
        if TS is not None:
            np_ = pos + len(snippet)
            editor.selection = TS(base_offset=np_, extend_offset=np_)
    except Exception:
        pass
    try: editor.update()
    except Exception: pass


def _contract_editor_ui(app, ct):
    page = app.page
    editor = K(ft.TextField, value=ct.template, multiline=True, text_size=11.5,
               text_align=ft.TextAlign.RIGHT, min_lines=12, max_lines=40,
               content_padding=pad_sym(10, 10), border_color=T()['line'], border_radius=10,
               hint_text="متن قالب قرارداد...")
    status = ft.Text("", size=10, color=T()['muted'])

    def refresh_status(e=None):
        ok, unknown = ct.validate_template(editor.value or '')
        if not (editor.value or '').strip():
            status.value = "⚠️ قالب خالی است"; status.color = T()['danger']
        elif ok:
            status.value = "✅ قالب معتبر"; status.color = T()['success']
        else:
            status.value = "⚠️ متغیر ناشناخته: " + ", ".join(sorted(unknown)); status.color = T()['danger']
        try: status.update()
        except Exception: pass
    editor.on_change = refresh_status
    refresh_status()

    def insert(snippet):
        _insert_snippet(editor, snippet); refresh_status()

    # ── پنل کنترل فشرده (حدود یک‌دهم ارتفاع صفحه)، قابل باز و بسته شدن ──
    groups = list(ct.VARIABLE_GROUPS)
    cats = [("🎯 چینش", None)] + [(g[0], i) for i, g in enumerate(groups)]
    sel = {'cat': 0}
    area_h = max(64, int((page.height or 700) * 0.075))
    cat_row = ft.Row(spacing=4, scroll=ft.ScrollMode.AUTO)
    chips_row = ft.Row(wrap=True, spacing=4, run_spacing=4)
    chips_box = ft.Container(content=ft.Column([chips_row], scroll=ft.ScrollMode.AUTO), height=area_h)

    def chip(label, snippet, bg):
        return ft.Container(content=txt(label, 9.5, True, T()['primary']), bgcolor=bg,
                            padding=pad_sym(7, 3), border_radius=10, ink=True,
                            on_click=lambda e, s=snippet: insert(s))

    def fill_panel():
        cat_row.controls.clear(); chips_row.controls.clear()
        for idx, (title, _g) in enumerate(cats):
            act = sel['cat'] == idx
            cat_row.controls.append(ft.Container(
                content=txt(title, 10, True, '#ffffff' if act else T()['primary']),
                bgcolor=T()['primary'] if act else alpha(T()['accent'], 0x44),
                padding=pad_sym(9, 4), border_radius=12, ink=True,
                on_click=lambda e, i=idx: pick(i)))
        if sel['cat'] == 0:
            for lbl, snip in CONTRACT_MARKERS_FA:
                chips_row.controls.append(chip(lbl, snip, alpha(T()['purple'], 0x44)))
        else:
            for name, lbl in groups[sel['cat'] - 1][1]:
                chips_row.controls.append(chip(lbl, "{{" + name + "}}", alpha(T()['accent'], 0x55)))

    def pick(i):
        sel['cat'] = i; fill_panel()
        try: cat_row.update(); chips_row.update()
        except Exception: pass
    fill_panel()

    body = ft.Column([cat_row, chips_box], spacing=4)
    arrow = ft.Icon(_ic('EXPAND_LESS'), size=18, color=T()['primary'])

    def toggle(e=None):
        body.visible = not body.visible
        ic = _ic('EXPAND_LESS') if body.visible else _ic('EXPAND_MORE')
        for attr in ('icon', 'name'):
            try:
                if hasattr(arrow, attr): setattr(arrow, attr, ic)
            except Exception: pass
        try: body.update(); arrow.update()
        except Exception: pass

    panel = ft.Container(
        content=ft.Column([
            ft.Container(ft.Row([txt("🎛 پنل کنترل — کلیک روی هر مورد = درج در متن", 10, True, T()['primary'], expand=True),
                                 arrow]),
                         on_click=toggle, ink=True, padding=pad_sym(2, 2)),
            body], spacing=4),
        padding=8, border_radius=10, bgcolor=T()['card'], border=border_all(1, T()['accent']))

    # ── اقدامات ──
    def do_save():
        ct.db.update('companies', ct.cid, {'contract_template': editor.value or ct.DEFAULT_TEMPLATE})
        app.toast("✅ قالب ذخیره شد")

    def save(ev=None):
        ok, unknown = ct.validate_template(editor.value or '')
        if unknown:
            app.confirm("متغیر ناشناخته وجود دارد:\n" + "\n".join(sorted(unknown)) +
                        "\n\nبا این حال ذخیره شود؟", do_save, "هشدار قالب"); return
        do_save()

    def reset_default(ev=None):
        def go():
            editor.value = ct.DEFAULT_TEMPLATE
            try: editor.update()
            except Exception: pass
            refresh_status(); app.toast("🔄 قالب پیش‌فرض بارگذاری شد")
        app.confirm("قالب پیش‌فرض رسمی بارگذاری شود؟ (متن فعلی ویرایش‌نشده از بین می‌رود)", go, "بازگردانی", False)

    def snap(ev=None):
        try:
            path = _png_path("contract")
            contract_png(path, ct, editor.value or ct.template)
            app.file_dialog(path, "📸 اسکرین‌شات کامل قرارداد")
        except Exception as ex:
            log_error(traceback.format_exc()); app.info("خطا در ساخت تصویر", str(ex))

    def preview(ev=None):
        try:
            pv = ct.preview_text(editor.value or ct.template, ct.company, ct.emp,
                                 (ct.dept or {}).get('title', ''))
            d = ft.AlertDialog(
                title=ft.Text("👁 پیش‌نمایش قرارداد", size=13),
                content=ft.Container(
                    ft.Column([ft.Container(txt(pv, 10.5, selectable=True), bgcolor='#ffffff',
                                            padding=14, border_radius=8,
                                            border=border_all(1, T()['line']))],
                              scroll=ft.ScrollMode.AUTO, spacing=6, tight=True),
                    width=min((page.width or 400) - 40, 500),
                    height=min((page.height or 700) * 0.7, 620)),
                actions=[tbtn("📸 اسکرین‌شات", lambda e: (app.close_dlg(d), snap())),
                         tbtn("بستن", lambda e: app.close_dlg(d))])
            app.open_dlg(d)
        except Exception as ex:
            log_error(traceback.format_exc()); app.toast(f"خطا: {ex}", True)

    def make_pdf(ev=None):
        try:
            path = os.path.join(export_dir(), f"contract_{(ct.emp or {}).get('id', 'sample')}_{datetime.now():%Y%m%d_%H%M%S}.pdf")
            ct.render_pdf(path, editor.value or ct.template)
            app.file_dialog(path, "📄 قرارداد PDF ساخته شد")
        except Exception as ex:
            log_error(traceback.format_exc()); app.info("خطا در ساخت PDF", str(ex))

    toolbar = ft.Row([
        gbtn("💾 ذخیره", _ic("SAVE"), save, T()['success'], height=38),
        obtn("👁 پیش‌نمایش", _ic("VISIBILITY"), preview, height=38),
        gbtn("📄 PDF", _ic("PICTURE_AS_PDF"), make_pdf, T()['primary'], height=38),
        obtn("📸 تصویر", _ic("PHOTO_CAMERA"), snap, height=38),
        obtn("🔄 پیش‌فرض", _ic("RESTORE"), reset_default, height=38),
    ], spacing=6, run_spacing=6, wrap=True)
    return dict(editor=editor, status=status, panel=panel, toolbar=toolbar)


def _contract_open(self):
    ui = _contract_editor_ui(self.app, self)
    title = (f"📄 قرارداد — {self.emp.get('first_name', '')} {self.emp.get('last_name', '')}"
             if self.emp else "📄 مدیریت قالب قرارداد")
    dlg = ft.AlertDialog(
        modal=True,
        title=ft.Row([ft.Text(title, size=13, expand=True), ui['status']],
                     vertical_alignment=ft.CrossAxisAlignment.CENTER),
        content=ft.Container(
            ft.Column([ui['toolbar'], ui['panel'], txt("✍️ متن قالب", 10, True, T()['muted']), ui['editor']],
                      scroll=ft.ScrollMode.AUTO, spacing=8, tight=True),
            width=min((self.page.width or 400) - 20, 560),
            height=min(max(((self.page.height or 700) - (self.app._kb_height or 0)) * 0.82, 280), 680)),
        actions=[tbtn("بستن", lambda e: self.app.close_dlg(dlg))])
    self.app.open_dlg(dlg)

Contract.open = _contract_open


def _app_v_contract_manager(self):
    rows = self.db.q("SELECT * FROM employees WHERE company_id=? AND is_active=1 ORDER BY id LIMIT 1", (self.cid,))
    emp = rows[0] if rows else dict(
        id='نمونه', first_name='نام', last_name='نمونه', father_name='پدر', national_code='0000000000',
        id_number='123', id_issue_place='تهران', birth_date='1370/01/01', birth_place='تهران',
        address='آدرس نمونه', mobile='09120000000', job_title='کارشناس', employment_date=jalali_today_str(),
        contract_end='', daily_salary=STD['min_daily_wage'], insurance_number='12345678901')
    ct = Contract(self, emp)
    ui = _contract_editor_ui(self, ct)
    return ft.Column([
        txt("قالب پیش‌فرض قرارداد همه پرسنل. در پیش‌نمایش و PDF از اطلاعات یک پرسنل نمونه استفاده می‌شود.",
            10, color=T()['muted']),
        ui['toolbar'], ui['panel'], ui['status'], ui['editor'],
        ft.Container(height=160),
    ], spacing=8, scroll=ft.ScrollMode.AUTO, expand=True)

App.v_contract_manager = _app_v_contract_manager



# ═══════════════════════ جستجوی کلمه‌به‌کلمه ═══════════════════════
_FA_FIX = str.maketrans({'ي': 'ی', 'ك': 'ک', 'ە': 'ه', 'ۀ': 'ه', '‌': ' ', '‏': '', '‎': ''})

def _fa_norm(s):
    return norm(s).translate(_FA_FIX).lower()

def _match_words(hay, q):
    """همه کلمه‌های جستجو (به هر ترتیب) باید در متن پیدا شوند."""
    words = _fa_norm(q).split()
    if not words:
        return True
    h = _fa_norm(hay)
    return all(w in h for w in words)


# ═══════════════════════ تصویر پرسنل و لوگو (سازگار با اندروید) ═══════════════════════
def _img_ctl(photo, w, h, radius=0):
    s = photo or ''
    if s.startswith('data:'):
        s = s.split(',', 1)[1]
    ps = _params(ft.Image)
    enum = getattr(ft, 'ImageFit', None) or getattr(ft, 'BoxFit', None)
    kw = dict(width=w, height=h)
    if enum is not None and hasattr(enum, 'COVER'):
        kw['fit'] = enum.COVER
    if 'src_base64' in ps:
        kw['src_base64'] = s
    else:
        try: kw['src'] = base64.b64decode(s)
        except Exception: kw['src'] = s
    if radius:
        kw['border_radius'] = radius
    return K(ft.Image, **kw)


def _compress_image_bytes(data, max_size=(360, 360), quality=78):
    if Image is not None:
        try:
            img = Image.open(io.BytesIO(data))
            img.thumbnail(max_size)
            if img.mode in ('RGBA', 'LA', 'P'):
                img = img.convert('RGBA')
                bg = Image.new('RGB', img.size, (255, 255, 255))
                bg.paste(img, mask=img.split()[-1])
                img = bg
            buf = io.BytesIO()
            img.convert('RGB').save(buf, format='JPEG', quality=quality, optimize=True)
            return buf.getvalue()
        except Exception:
            pass
    return data


async def _pick_image(page, callback=None):
    """انتخاب عکس از گالری؛ هم نسخه‌های قدیمی (رویداد) و هم جدید (مقدار برگشتی)."""
    picker = K(ft.FilePicker, on_result=callback)
    _attach_picker(page, picker)
    try: page.update()
    except Exception: pass
    ps = _params(picker.pick_files)
    kw = {}
    if 'allow_multiple' in ps: kw['allow_multiple'] = False
    FT = getattr(ft, 'FilePickerFileType', None)
    if FT is not None and 'file_type' in ps and hasattr(FT, 'IMAGE'):
        kw['file_type'] = FT.IMAGE
    elif 'allowed_extensions' in ps:
        kw['allowed_extensions'] = ['jpg', 'jpeg', 'png', 'webp']
    if 'with_data' in ps: kw['with_data'] = True
    res = await _await_if(picker.pick_files(**kw))
    if not res:
        return []
    if isinstance(res, (list, tuple)):
        return list(res)
    return list(getattr(res, 'files', None) or [])


async def _app_pick_photo(self, emp_id):
    try:
        files = await _pick_image(self.page, lambda e: self._on_photo_picked(e, emp_id))
        if files:
            self._store_employee_photo(emp_id, files[0])
    except Exception:
        log_error(traceback.format_exc())
        self.toast('انتخاب عکس انجام نشد. اجازه دسترسی به عکس‌ها را بررسی کنید.', True)


def _app_store_employee_photo(self, emp_id, file_obj):
    try:
        data = _picked_bytes(file_obj)
        if not data:
            self.toast('محتوای عکس دریافت نشد.', True); return
        data = _compress_image_bytes(data)
        self.db.update('employees', emp_id, {'photo': _image_data_uri(data)})
        self.toast('✅ عکس پرسنل ذخیره شد')
        d = getattr(self, '_emp_dlg', None)
        if d is not None:
            self.close_dlg(d); self._emp_dlg = None
        self.render()
        fresh = self.db.q1("SELECT * FROM employees WHERE id=?", (emp_id,))
        if fresh:
            self.emp_detail(fresh)
    except Exception:
        log_error(traceback.format_exc()); self.toast('ذخیره عکس ناموفق بود.', True)


async def _app_pick_logo(self):
    try:
        files = await _pick_image(self.page, self._on_logo_picked)
        if files:
            self._store_company_logo(files[0])
    except Exception:
        log_error(traceback.format_exc())
        self.toast('انتخاب لوگو انجام نشد. اجازه دسترسی به عکس‌ها را بررسی کنید.', True)


def _app_store_company_logo(self, file_obj):
    try:
        data = _picked_bytes(file_obj)
        if not data:
            self.toast('محتوای فایل لوگو دریافت نشد.', True); return
        data = _compress_image_bytes(data, (600, 400), 88)
        self.db.update('companies', self.cid, {'logo': _image_data_uri(data)})
        self.toast('✅ لوگوی شرکت ذخیره شد')
        self.render()
    except Exception:
        log_error(traceback.format_exc()); self.toast('ذخیره لوگو ناموفق بود.', True)


App._pick_photo = _app_pick_photo
App._store_employee_photo = _app_store_employee_photo
App._pick_logo = _app_pick_logo
App._store_company_logo = _app_store_company_logo


def _app_v_company(self):
    c = self.db.q1("SELECT * FROM companies WHERE id=?", (self.cid,)) or {}
    logo = c.get('logo') or ''
    if logo:
        prev = _img_ctl(logo, 130, 100, 8)
    else:
        prev = ft.Container(txt('لوگو ثبت نشده', 11, color=T()['muted']), width=130, height=100,
                            alignment=center(), bgcolor=T()['bg'], border_radius=8,
                            border=border_all(1, T()['line']))

    async def pick(e):
        await self._pick_logo()

    def remove(e):
        def go():
            self.db.update('companies', self.cid, {'logo': ''})
            self.toast('لوگو حذف شد'); self.render()
        self.confirm('لوگوی شرکت حذف شود؟', go, 'حذف لوگو')

    def line(label, val):
        return ft.Row([txt(label, 11, color=T()['muted'], width=100),
                       txt(str(val or '-'), 11, True, expand=True)], spacing=4)

    logo_btns = [gbtn('📷 انتخاب لوگو', _ic('PHOTO_CAMERA'), pick, T()['primary'])]
    if logo:
        logo_btns.append(obtn('🗑 حذف لوگو', _ic('DELETE'), remove))
    return ft.ListView([
        card(ft.Column([
            txt('🖼 لوگوی شرکت', 13, True),
            ft.Row([prev, ft.Column(logo_btns, spacing=6, expand=True)], spacing=12),
            txt('لوگو روی فیش حقوقی و قرارداد چاپ می‌شود.', 10, color=T()['muted']),
        ], spacing=8), padding=12),
        card(ft.Column([
            txt('🏢 اطلاعات شرکت', 13, True),
            line('نام شرکت', c.get('name')), line('شناسه ملی', c.get('reg_no')),
            line('کد اقتصادی', c.get('economic_code')), line('تلفن', c.get('phone')),
            line('آدرس', c.get('address')), line('مدیرعامل', c.get('sign_manager')),
            line('حسابدار', c.get('sign_accountant')),
            gbtn('✏️ ویرایش اطلاعات', _ic('EDIT'), lambda e: self.company_edit_form(), T()['success']),
        ], spacing=6), padding=12),
    ], spacing=8, expand=True, padding=pad_only(bottom=20))


App.company_edit_form = App.company_form
App.company_form = lambda self: self.push("اطلاعات و لوگوی شرکت", self.v_company)
App.v_company = _app_v_company


# ═══════════════════════ اسکرین‌شات تومارِ کامل (ساخت مستقیم تصویر) ═══════════════════════
def render_doc_png(path, blocks, width=900):
    """تصویر بلند و کامل از سند؛ مستقل از صفحه نمایش، مناسب اندروید."""
    if Image is None:
        raise RuntimeError('کتابخانه تصویر در دسترس نیست.')
    from PIL import ImageDraw, ImageFont
    fpath = find_font()
    if not fpath:
        raise RuntimeError('فونت فارسی پیدا نشد.')
    fonts = {}
    def F(sz):
        if sz not in fonts: fonts[sz] = ImageFont.truetype(fpath, sz)
        return fonts[sz]
    NAVY, GOLD, TXT, MUT = (30, 58, 95), (240, 180, 41), (20, 30, 45), (100, 116, 139)
    LINE, SOFT, CREAM = (170, 185, 205), (244, 248, 252), (255, 248, 220)
    M = 30; CW = width - 2 * M

    def run(d):
        def tw(s, sz): return F(sz).getlength(rtl(s))
        def right(xr, y, s, sz, col): d.text((xr - tw(s, sz), y), rtl(s), font=F(sz), fill=col)
        def left(xl, y, s, sz, col): d.text((xl, y), rtl(s), font=F(sz), fill=col)
        def mid(x0, x1, y, s, sz, col): d.text(((x0 + x1 - tw(s, sz)) / 2, y), rtl(s), font=F(sz), fill=col)
        def wrap(text, sz, maxw):
            out = []
            for para in str(text).split('\n'):
                cur = ''
                for w in para.split():
                    t = (cur + ' ' + w).strip()
                    if cur and tw(t, sz) > maxw: out.append(cur); cur = w
                    else: cur = t
                out.append(cur)
            return out
        y = M
        for b in blocks:
            k = b[0]
            if k == 'header':
                d.rectangle([M, y, M + CW, y + 120], fill=NAVY)
                mid(M, M + CW, y + 18, b[1], 34, (255, 220, 130))
                mid(M, M + CW, y + 72, b[2], 22, (225, 232, 245))
                d.rectangle([M, y + 120, M + CW, y + 124], fill=GOLD)
                y += 124 + 22
            elif k == 'band':
                col = b[2] if len(b) > 2 else NAVY
                d.rectangle([M, y, M + CW, y + 44], fill=col)
                mid(M, M + CW, y + 6, b[1], 22, (255, 255, 255))
                y += 44 + 4
            elif k == 'rows':
                for i, (name, amt) in enumerate(b[1]):
                    d.rectangle([M, y, M + CW, y + 42], fill=SOFT if i % 2 == 0 else (255, 255, 255), outline=LINE)
                    right(M + CW - 14, y + 7, name, 21, TXT)
                    left(M + 14, y + 7, amt, 21, b[2] if len(b) > 2 else TXT)
                    y += 42
                y += 14
            elif k == 'grid':
                for row in b[1]:
                    n = max(1, len(row)); cw_ = CW / n
                    for j, cell in enumerate(row):
                        x0 = M + j * cw_
                        d.rectangle([x0, y, x0 + cw_, y + 44], fill=SOFT, outline=LINE)
                        lines = wrap(cell, 20, cw_ - 20)
                        right(x0 + cw_ - 10, y + 8, lines[0] if lines else '', 20, TXT)
                    y += 44
                y += 14
            elif k == 'para':
                sz = b[2] if len(b) > 2 else 21
                al = b[3] if len(b) > 3 else 'R'
                for ln in wrap(b[1], sz, CW - 20):
                    if al == 'C': mid(M, M + CW, y, ln, sz, TXT)
                    else: right(M + CW - 10, y, ln, sz, TXT)
                    y += int(sz * 1.75)
                y += 8
            elif k == 'box':
                lines = wrap(b[1], 21, CW - 50)
                h = int(len(lines) * 37 + 24)
                d.rectangle([M, y, M + CW, y + h], fill=CREAM, outline=GOLD, width=2)
                yy = y + 12
                for ln in lines:
                    right(M + CW - 22, yy, ln, 21, TXT); yy += 37
                y += h + 14
            elif k == 'total':
                d.rectangle([M, y, M + CW, y + 78], fill=b[3] if len(b) > 3 else CREAM, outline=GOLD, width=3)
                mid(M, M + CW, y + 20, f"{b[1]}:   {b[2]}", 30, b[4] if len(b) > 4 else TXT)
                y += 78 + 14
            elif k == 'title':
                mid(M, M + CW, y, b[1], b[2] if len(b) > 2 else 28, b[3] if len(b) > 3 else NAVY)
                y += int((b[2] if len(b) > 2 else 28) * 1.7)
            elif k == 'note':
                mid(M, M + CW, y, b[1], 17, MUT); y += 32
            elif k == 'hr':
                d.line([M + 30, y + 8, M + CW - 30, y + 8], fill=GOLD, width=2); y += 20
        return y + M

    h = run(ImageDraw.Draw(Image.new('RGB', (1, 1))))
    img = Image.new('RGB', (width, int(h)), (255, 255, 255))
    d = ImageDraw.Draw(img)
    run(d)
    d.rectangle([8, 8, width - 9, int(h) - 9], outline=(55, 80, 110), width=3)
    img.save(path, 'PNG')
    return path


def slip_png(path, company, pay, emp, dept, dets, loan_insts=None):
    pay = pay or {}; emp = emp or {}
    rows = [("حقوق پایه", fmt(pay.get('base_salary_monthly', 0)))]
    rows += [(d['name'], fmt(d['amount'])) for d in dets if d.get('type') == 1 and (d.get('amount') or 0) > 0]
    for lbl, key in (("اضافه‌کاری", 'overtime_amount'), ("شب‌کاری", 'night_amount'),
                     ("نوبت‌کاری", 'shift_amount'), ("جمعه‌کاری", 'friday_amount'),
                     ("تعطیل‌کاری", 'holiday_amount'), ("مأموریت", 'mission_amount')):
        if pay.get(key): rows.append((lbl, fmt(pay[key])))
    ded = [(d['name'], fmt(d['amount'])) for d in dets if d.get('type') == 2
           and (d.get('amount') or 0) > 0 and not (d.get('name') or '').startswith('قسط')]
    for li in (loan_insts or []):
        ded.append((f"قسط وام شماره {li.get('installment_no', '')}", fmt(li.get('amount', 0))))
    if not loan_insts and (pay.get('loan_install') or 0) > 0:
        ded.append(("قسط وام", fmt(pay['loan_install'])))
    total_ded = (pay.get('gross_salary') or 0) - (pay.get('net_salary') or 0)
    work = [("کارکرد", f"{pay.get('work_days') or 0:g} روز"),
            ("اضافه‌کاری", hours_to_hm(pay.get('overtime_hours') or 0)),
            ("شب‌کاری", hours_to_hm(pay.get('night_hours') or 0)),
            ("جمعه‌کاری", hours_to_hm(pay.get('friday_hours') or 0)),
            ("تعطیل‌کاری", hours_to_hm(pay.get('holiday_hours') or 0)),
            ("کسر کار", hours_to_hm(pay.get('absent_hours') or 0)),
            ("مأموریت", f"{pay.get('mission_days') or 0:g} روز")]
    blocks = [
        ('header', company.get('name') or APP_TITLE,
         f"فیش حقوق و دستمزد — {MONTHS[int(pay.get('month', 1)) - 1]} {pay.get('year', '')}"),
        ('grid', [[f"نام: {emp.get('first_name', '')} {emp.get('last_name', '')}",
                   f"کد پرسنلی: {emp.get('personnel_code') or emp.get('id') or '-'}"],
                  [f"کد ملی: {emp.get('national_code') or '-'}", f"واحد: {(dept or {}).get('title') or '-'}"],
                  [f"سمت: {emp.get('job_title') or '-'}", f"شماره بیمه: {emp.get('insurance_number') or '-'}"],
                  [f"شماره حساب: {emp.get('account_number') or '-'}", f"وضعیت: {'پرداخت شده' if pay.get('payment_status') == 'paid' else 'در انتظار پرداخت'}"]]),
        ('band', 'اطلاعات کارکرد', (28, 78, 111)), ('rows', work, (25, 70, 130)),
        ('band', 'حقوق و مزایا', (28, 78, 111)), ('rows', rows),
        ('band', 'کسورات', (192, 57, 43)), ('rows', ded or [('-', '0')], (160, 35, 35)),
        ('grid', [[f"جمع پرداختی: {fmt(pay.get('gross_salary', 0))}", f"جمع کسورات: {fmt(total_ded)}"]]),
        ('total', 'خالص پرداختی', f"{fmt(pay.get('net_salary', 0))} ریال", (255, 241, 207), (22, 110, 70)),
        ('note', f"{APP_TITLE} • {DEVELOPER} • {DEVELOPER_PHONE}"),
    ]
    return render_doc_png(path, blocks)


def contract_png(path, ct, template):
    text = ct._render_text(template or ct.template)
    c = ct.company or {}; e = ct.emp or {}
    blocks = [('header', c.get('name') or APP_TITLE, 'قرارداد کار')]
    for kind, content in Contract.parse(text):
        if kind == 'title': blocks.append(('title', content, 30))
        elif kind == 'section': blocks.append(('band', content, (184, 134, 11)))
        elif kind == 'article': blocks.append(('band', content, (60, 95, 140)))
        elif kind == 'para': blocks.append(('para', content[0], 21, content[1]))
        elif kind == 'box': blocks.append(('box', content))
        elif kind == 'hr': blocks.append(('hr',))
        elif kind == 'table': blocks.append(('grid', content))
    blocks.append(('grid', [[f"کارفرما: {c.get('sign_manager') or c.get('name') or '—'}",
                             f"کارگر: {e.get('first_name', '')} {e.get('last_name', '')}".strip()]]))
    blocks.append(('note', f"{APP_TITLE} • {DEVELOPER} • {DEVELOPER_PHONE}"))
    return render_doc_png(path, blocks)


def report_png(path, company, year, month, pays, by_dept):
    def s(k): return fmt(sum(p.get(k, 0) or 0 for p in pays))
    blocks = [('header', company.get('name') or APP_TITLE, f"گزارش حقوق — {MONTHS[month - 1]} {year}"),
              ('band', 'خلاصه'),
              ('rows', [("تعداد فیش", str(len(pays))), ("جمع ناخالص", s('gross_salary')),
                        ("بیمه کارگر", s('insurance_emp')), ("بیمه کارفرما", s('insurance_er')),
                        ("مالیات", s('tax')), ("اقساط وام", s('loan_install'))]),
              ('total', 'جمع خالص', s('net_salary'), (255, 241, 207), (22, 110, 70))]
    if by_dept:
        blocks.append(('band', 'خالص به تفکیک واحد'))
        blocks.append(('rows', [(f"{t} ({v[0]} نفر)", fmt(v[2])) for t, v in sorted(by_dept.items())]))
    blocks.append(('note', f"{APP_TITLE} • {DEVELOPER} • {DEVELOPER_PHONE}"))
    return render_doc_png(path, blocks)


def _png_path(name):
    return os.path.join(export_dir(), f"{name}_{datetime.now():%Y%m%d_%H%M%S}.png")



def main(page: ft.Page):
    if WEB.get('blocked') and getattr(page, 'web', False):
        page.add(ft.Text('دسترسی از طریق وب غیرفعال شده است.', size=14))
        page.update(); return
    try:
        App(page, Database()).start()
    except Exception:
        tb = traceback.format_exc(); log_error(tb)
        try:
            page.add(ft.Text("خطای راه‌اندازی:\n" + tb, selectable=True, size=11))
            page.update()
        except Exception: pass

App.v_payroll = _app_v_payroll



# ═══════════════════════════════════════════════════════════════════════════════
# ERFAN HESAB PRO — پایداری، سرعت، ذخیره‌سازی و دسترسی‌های سریع
# این لایه روی هسته و پایگاه‌داده قبلی سوار می‌شود و ساختار دیتابیس را حفظ می‌کند.
# ═══════════════════════════════════════════════════════════════════════════════

_ATTENDANCE_UPSERT_SQL = """INSERT INTO attendances (
    company_id, emp_id, year, month, work_days, overtime_hours, night_hours,
    absent_hours, mission_days, shift_percent, friday_hours, holiday_hours,
    overtime_minutes, night_minutes, absent_minutes, friday_rest_replaced,
    holiday_rest_replaced, notes
) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
ON CONFLICT(company_id, emp_id, year, month) DO UPDATE SET
    work_days=excluded.work_days,
    overtime_hours=excluded.overtime_hours,
    night_hours=excluded.night_hours,
    absent_hours=excluded.absent_hours,
    mission_days=excluded.mission_days,
    shift_percent=excluded.shift_percent,
    friday_hours=excluded.friday_hours,
    holiday_hours=excluded.holiday_hours,
    overtime_minutes=excluded.overtime_minutes,
    night_minutes=excluded.night_minutes,
    absent_minutes=excluded.absent_minutes,
    friday_rest_replaced=excluded.friday_rest_replaced,
    holiday_rest_replaced=excluded.holiday_rest_replaced,
    notes=excluded.notes"""


def _db_upsert_attendances(self, cid, records):
    """ذخیره اتمیک و گروهی کارکرد؛ سریع‌تر و امن‌تر در برابر قطع برنامه."""
    records = list(records or [])
    if not records:
        return 0
    rows = []
    for a in records:
        rows.append((
            cid, int(a['emp_id']), int(a['year']), int(a['month']),
            max(0.0, _as_float(a.get('work_days'))),
            max(0.0, _as_float(a.get('overtime_hours'))),
            max(0.0, _as_float(a.get('night_hours'))),
            max(0.0, _as_float(a.get('absent_hours'))),
            max(0.0, _as_float(a.get('mission_days'))),
            max(0.0, _as_float(a.get('shift_percent'))),
            max(0.0, _as_float(a.get('friday_hours'))),
            max(0.0, _as_float(a.get('holiday_hours'))),
            max(0, int(_as_float(a.get('overtime_minutes')))),
            max(0, int(_as_float(a.get('night_minutes')))),
            max(0, int(_as_float(a.get('absent_minutes')))),
            int(bool(a.get('friday_rest_replaced'))),
            int(bool(a.get('holiday_rest_replaced'))),
            str(a.get('notes') or '')
        ))
    with self.tx() as conn:
        conn.executemany(_ATTENDANCE_UPSERT_SQL, rows)
    return len(rows)


Database.upsert_attendances = _db_upsert_attendances


def _validated_save_loan(self, cid, emp_id, principal, count, sy, sm, purpose=''):
    principal, count, sy, sm = int(principal), int(count), int(sy), int(sm)
    if principal <= 0:
        raise ValueError('مبلغ وام باید بیشتر از صفر باشد.')
    if not 1 <= count <= 600:
        raise ValueError('تعداد اقساط باید بین ۱ تا ۶۰۰ باشد.')
    if not 1300 <= sy <= 1500 or not 1 <= sm <= 12:
        raise ValueError('تاریخ شروع اقساط معتبر نیست.')
    if not self.q1('SELECT id FROM employees WHERE id=? AND company_id=?', (emp_id, cid)):
        raise ValueError('پرسنل انتخاب‌شده معتبر نیست.')
    return _DB_SAVE_LOAN_ORIGINAL(self, cid, emp_id, principal, count, sy, sm, purpose)


_DB_SAVE_LOAN_ORIGINAL = Database.save_loan
Database.save_loan = _validated_save_loan


def _human_bytes(size):
    try:
        n = float(size)
    except Exception:
        return '۰ بایت'
    for unit in ('بایت', 'کیلوبایت', 'مگابایت', 'گیگابایت', 'ترابایت'):
        if n < 1024 or unit == 'ترابایت':
            if unit == 'بایت':
                return f'{int(n):,} {unit}'
            return f'{n:.1f} {unit}'
        n /= 1024.0
    return f'{n:.1f} گیگابایت'


def _export_files_summary(directory=None):
    directory = directory or export_dir()
    os.makedirs(directory, exist_ok=True)
    files = []
    total = 0
    for name in os.listdir(directory):
        path = os.path.join(directory, name)
        try:
            if not os.path.isfile(path):
                continue
            st = os.stat(path)
            item = {'name': name, 'path': path, 'size': st.st_size,
                    'mtime': st.st_mtime, 'ext': os.path.splitext(name)[1].lower()}
            files.append(item)
            total += st.st_size
        except OSError:
            continue
    files.sort(key=lambda x: x['mtime'], reverse=True)
    return files, total


def _app_v_storage(self):
    """مدیریت خروجی‌های چاپ و گزارش با امکان اشتراک، حذف و پاک‌سازی امن."""
    state = {'q': ''}
    body = ft.Column(spacing=6, expand=True, scroll=ft.ScrollMode.AUTO)
    search = tf('جستجوی فایل‌ها...', '', prefix=_ic('SEARCH'), size=12,
                on_change=lambda e: (state.update({'q': e.control.value or ''}),
                                     self.debounce('files_q', render_list)))
    summary = ft.Container()
    listing = ft.Column(spacing=5)

    def open_one(path, ev=None):
        if os.path.isfile(path):
            self.file_dialog(path, 'فایل ذخیره‌شده')
        else:
            self.toast('این فایل دیگر وجود ندارد.', True)

    def remove_one(path, ev=None):
        name = os.path.basename(path)
        if os.path.splitext(name)[1].lower() == '.db' or name.endswith('.before_restore'):
            self.toast('حذف فایل پشتیبان از این بخش غیرفعال است تا نسخه پشتیبان تصادفی از بین نرود.', True)
            return
        def go():
            try:
                os.remove(path)
                self.toast(f'فایل «{name}» حذف شد.')
                render_list()
            except Exception as ex:
                self.toast(f'حذف فایل انجام نشد: {ex}', True)
        self.confirm(f'فایل «{name}» حذف شود؟ این کار قابل بازگشت نیست.', go, 'حذف فایل')

    def clean_old(ev=None):
        files, _ = _export_files_summary()
        cutoff = time.time() - 30 * 86400
        eligible = [f for f in files if f['mtime'] < cutoff and f['ext'] in ('.pdf', '.png', '.csv')]
        if not eligible:
            self.toast('فایل PDF، تصویر یا CSV قدیمی‌تر از ۳۰ روز پیدا نشد.')
            return
        def go():
            deleted = freed = 0
            errors = 0
            for f in eligible:
                try:
                    os.remove(f['path'])
                    deleted += 1
                    freed += f['size']
                except OSError:
                    errors += 1
            self.toast(f'{deleted} فایل حذف شد؛ { _human_bytes(freed) } فضا آزاد شد.' +
                       (f' {errors} فایل حذف نشد.' if errors else ''))
            render_list()
        self.confirm(f'{len(eligible)} خروجی چاپی/گزارشی قدیمی‌تر از ۳۰ روز حذف شود؟\n\nفایل‌های پشتیبان دیتابیس حذف نمی‌شوند.',
                     go, 'پاک‌سازی فضای ذخیره‌سازی')

    def render_list():
        files, total = _export_files_summary()
        q = (state['q'] or '').strip().casefold()
        if q:
            files = [f for f in files if q in f['name'].casefold()]
        shown = files[:100]
        summary.content = card(ft.Column([
            ft.Row([
                ft.Column([txt('فایل‌های ذخیره‌شده', 11, color=T()['muted']),
                           txt(f'{len(files):,}', 18, True, T()['primary'])], spacing=1, expand=True),
                ft.Column([txt('حجم پوشه خروجی', 11, color=T()['muted']),
                           txt(_human_bytes(total), 15, True, T()['success'])], spacing=1),
            ], spacing=8),
            txt(export_dir(), 9, color=T()['muted'], selectable=True),
        ], spacing=6), padding=10)
        listing.controls.clear()
        if not shown:
            listing.controls.append(card(ft.Column([
                ft.Icon(_ic('FOLDER_OPEN'), size=30, color=T()['muted']),
                txt('فایلی با این جستجو پیدا نشد.', 12, color=T()['muted'])
            ], horizontal_alignment=ft.CrossAxisAlignment.CENTER, spacing=6), padding=18))
        for item in shown:
            pth = item['path']
            when = datetime.fromtimestamp(item['mtime']).strftime('%Y/%m/%d  %H:%M')
            ext = item['ext'].upper().lstrip('.') or 'FILE'
            ico = {'PDF': 'PICTURE_AS_PDF', 'PNG': 'IMAGE', 'CSV': 'TABLE_CHART', 'DB': 'STORAGE'}.get(ext, 'INSERT_DRIVE_FILE')
            listing.controls.append(card(ft.Row([
                ft.Container(ft.Icon(_ic(ico), size=22, color=T()['primary']),
                             width=38, height=38, bgcolor=alpha(T()['primary'], 0x12),
                             border_radius=10, alignment=center()),
                ft.Column([
                    txt(item['name'], 11, True, max_lines=2, overflow=ft.TextOverflow.ELLIPSIS),
                    txt(f'{_human_bytes(item["size"])}  •  {when}', 9, color=T()['muted']),
                ], spacing=2, expand=True),
                iconbtn(_ic('OPEN_IN_NEW'), lambda e, p=pth: open_one(p, e), T()['success'], 18, 'بازکردن/چاپ/اشتراک'),
                iconbtn(_ic('DELETE_OUTLINE', 'DELETE'), lambda e, p=pth: remove_one(p, e), T()['danger'], 18, 'حذف فایل'),
            ], spacing=6, vertical_alignment=ft.CrossAxisAlignment.CENTER), padding=8))
        if len(files) > 100:
            listing.controls.append(txt(f'برای سرعت، ۱۰۰ فایل جدید نمایش داده شد؛ با جستجو فایل قدیمی‌تر را پیدا کنید. (کل نتایج: {len(files)})',
                                        10, color=T()['muted']))
        try:
            summary.update()
            listing.update()
        except Exception:
            pass

    render_list()
    return ft.Column([
        card(ft.Column([
            ft.Row([txt('مرکز فایل‌ها', 14, True, expand=True),
                    iconbtn(_ic('REFRESH'), lambda e: render_list(), T()['primary'], 20, 'به‌روزرسانی')]),
            txt('PDF فیش‌ها و قراردادها، تصاویر فیش، فایل‌های CSV و پشتیبان‌ها از اینجا قابل مدیریت‌اند.',
                10, color=T()['muted']),
            search,
            ft.Row([
                gbtn('پاک‌سازی خروجی‌های بالای ۳۰ روز', _ic('DELETE_SWEEP'), clean_old,
                     T()['danger'], expand=True, height=36),
            ]),
        ], spacing=8), padding=10),
        summary,
        listing,
    ], spacing=6, expand=True, scroll=ft.ScrollMode.AUTO)


App.v_storage = _app_v_storage

# اضافه‌کردن مرکز فایل‌ها بدون حذف امکانات موجود در تب «بیشتر».
_APP_V_MORE_ORIGINAL = App.v_more

def _app_v_more_with_storage(self):
    view = _APP_V_MORE_ORIGINAL(self)
    try:
        items = list(getattr(view, 'controls', []) or [])
        shortcut = card(ft.Row([
            ft.Container(ft.Icon(_ic('FOLDER_COPY'), color=T()['primary'], size=18),
                         bgcolor=T()['accent'], width=38, height=38,
                         border_radius=19, alignment=center()),
            ft.Column([txt('مرکز فایل‌ها و چاپ', 12, True),
                       txt('پیش‌نمایش، اشتراک‌گذاری، مدیریت و آزادسازی فضا', 10, color=T()['muted'])],
                      spacing=0, expand=True),
            ft.Icon(_ic('CHEVRON_LEFT'), color=T()['muted'], size=16),
        ], spacing=10), padding=10, on_click=lambda e: self.push('مرکز فایل‌ها و چاپ', self.v_storage))
        items.insert(max(0, len(items) - 1), shortcut)
        view.controls = items
    except Exception:
        log_error(traceback.format_exc())
    return view

App.v_more = _app_v_more_with_storage


# ── مسیر فایل محلی: پیش‌نمایش واقعی PDF و پشتیبانی از Range برای PDF Viewer اندروید ──
_FILE_META = {}

def _filehandler_get(self):
    try:
        raw_path = self.path.split('?', 1)[0]
        parts = urllib.parse.unquote(raw_path).split('/')
        token = parts[2] if len(parts) > 2 else ''
        path = _FILE_REG.get(token)
        if not path or not os.path.isfile(path):
            self.send_error(404)
            return
        size = os.path.getsize(path)
        ctype = mimetypes.guess_type(path)[0] or 'application/octet-stream'
        display_inline = ctype.startswith('image/') or ctype == 'application/pdf'
        filename = urllib.parse.quote(os.path.basename(path))
        start, end = 0, max(0, size - 1)
        status_code = 200
        header_range = self.headers.get('Range', '')
        if header_range.startswith('bytes=') and size:
            try:
                chunk = header_range[6:].split(',', 1)[0].strip()
                a, b = (chunk.split('-', 1) + [''])[:2]
                if a == '':
                    length = int(b)
                    start = max(0, size - length)
                else:
                    start = int(a)
                if b and a:
                    end = min(size - 1, int(b))
                else:
                    end = size - 1
                if start < 0 or start >= size or end < start:
                    raise ValueError('range')
                status_code = 206
            except Exception:
                self.send_response(416)
                self.send_header('Content-Range', f'bytes */{size}')
                self.send_header('Content-Length', '0')
                self.end_headers()
                return
        length = max(0, end - start + 1) if size else 0
        self.send_response(status_code)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(length))
        self.send_header('Content-Disposition',
                         ('inline' if display_inline else 'attachment') + "; filename*=UTF-8''" + filename)
        self.send_header('Accept-Ranges', 'bytes')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Cache-Control', 'no-store, max-age=0')
        if status_code == 206:
            self.send_header('Content-Range', f'bytes {start}-{end}/{size}')
        self.end_headers()
        if length:
            with open(path, 'rb') as handle:
                handle.seek(start)
                remaining = length
                while remaining:
                    chunk = handle.read(min(64 * 1024, remaining))
                    if not chunk:
                        break
                    self.wfile.write(chunk)
                    remaining -= len(chunk)
    except (BrokenPipeError, ConnectionResetError):
        pass
    except Exception:
        log_error('File preview endpoint failed:\n' + traceback.format_exc())

_FileHandler.do_GET = _filehandler_get

_FILE_URL_ORIGINAL = _file_url

def _enhanced_file_url(path):
    if not os.path.isfile(path):
        raise FileNotFoundError(path)
    now = time.time()
    for tok, stamp in list(_FILE_META.items()):
        if now - stamp > 24 * 3600 or len(_FILE_META) > 160:
            _FILE_META.pop(tok, None)
            _FILE_REG.pop(tok, None)
    if _FILE_SRV['srv'] is None:
        srv = http.server.ThreadingHTTPServer(('127.0.0.1', 0), _FileHandler)
        srv.daemon_threads = True
        threading.Thread(target=srv.serve_forever, name='ErfanHesab-FilePreview', daemon=True).start()
        _FILE_SRV['srv'] = srv
        _FILE_SRV['port'] = srv.server_address[1]
    token = secrets.token_urlsafe(18)
    _FILE_REG[token] = os.path.abspath(path)
    _FILE_META[token] = now
    return f"http://127.0.0.1:{_FILE_SRV['port']}/f/{token}/{urllib.parse.quote(os.path.basename(path))}"

_file_url = _enhanced_file_url


# ── شبکه محلی: تشخیص IP واقعی، بررسی HTTP و مدیریت درست کلید روشن/خاموش ──
def _enhanced_lan_ips():
    ips = []
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            # اتصال UDP فقط برای تشخیص IP مسیر خروجی است؛ بسته‌ای به مقصد ارسال نمی‌شود.
            sock.connect(('192.0.2.1', 9))
            ip = sock.getsockname()[0]
            if ip and not ip.startswith('127.') and ip != '0.0.0.0':
                ips.append(ip)
        finally:
            sock.close()
    except Exception:
        pass
    try:
        for row in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ip = row[4][0]
            if ip and not ip.startswith('127.') and ip != '0.0.0.0' and ip not in ips:
                ips.append(ip)
    except Exception:
        pass
    return ips


def _http_probe(port, path='/'):
    try:
        conn = http.client.HTTPConnection('127.0.0.1', int(port), timeout=0.8)
        conn.request('GET', path, headers={'Connection': 'close'})
        res = conn.getresponse()
        res.read(256)
        code = int(res.status)
        conn.close()
        return 200 <= code < 500
    except Exception:
        return False


_lan_ips = _enhanced_lan_ips

_WEB_SHARE_START_ORIGINAL = web_share_start
_WEB_SHARE_STOP_ORIGINAL = web_share_stop

def _enhanced_web_share_start(port):
    try:
        port = int(norm(port))
    except Exception:
        return False, 'شماره پورت معتبر نیست.'
    if not 1024 <= port <= 65535:
        return False, 'پورت باید بین ۱۰۲۴ تا ۶۵۵۳۵ باشد.'

    if _is_android():
        old_thread = WEB.get('thread')
        old_port = int(WEB.get('port') or 0)
        if old_thread is not None and old_thread.is_alive():
            if old_port != port:
                return False, (f'سرویس قبلی هنوز در پورت {old_port} اجراست. '
                               'برای تغییر پورت، برنامه را کاملاً ببندید و دوباره باز کنید.')
            if _http_probe(port) or _port_open(port):
                WEB['blocked'] = False
                return True, ''
            return False, 'ریسمان سرویس وب فعال است اما پاسخ HTTP دریافت نشد؛ برنامه را دوباره اجرا کنید.'
        if _port_open(port):
            return False, f'پورت {port} توسط برنامه دیگری استفاده می‌شود؛ پورت دیگری انتخاب کنید.'
        WEB['blocked'] = False
        WEB['port'] = port
        th = threading.Thread(target=_thread_web, args=(port,), name='ErfanHesab-Web', daemon=True)
        WEB['thread'] = th
        WEB['mode'] = 'thread'
        th.start()
        for _ in range(48):
            if not th.is_alive():
                WEB['blocked'] = True
                return False, ('سرویس وب در اندروید اجرا نشد. اجرای وب‌سرور دوم به پشتیبانی نسخه Flet/کلاینت نصب‌شده وابسته است. '
                               'گزارش خطا در پوشه برنامه و فایل error.log ثبت شده است.')
            if _http_probe(port):
                return True, ''
            time.sleep(0.25)
        WEB['blocked'] = True
        return False, (f'در پورت {port} پاسخ HTTP دریافت نشد. '
                       'برای اجرای مطمئن نسخه مرورگری، همین فایل را با فرمان «flet run --web --host 0.0.0.0 --port '
                       f'{port} erfanhesab_pro.py» از رایانه اجرا کنید.')

    # Desktop: reuse if same server is already on requested port; restart for a changed port.
    if web_share_active():
        if int(WEB.get('port') or 0) == port:
            return True, ''
        _WEB_SHARE_STOP_ORIGINAL()
    return _WEB_SHARE_START_ORIGINAL(port)


web_share_start = _enhanced_web_share_start


def _enhanced_web_share_stop():
    if _is_android():
        # Flet's API does not expose the server handle for a second in-process app.
        # block new web sessions; to release the listener completely, fully close the Android app.
        WEB['blocked'] = True
        return
    _WEB_SHARE_STOP_ORIGINAL()


web_share_stop = _enhanced_web_share_stop


def _app_v_webshare_pro(self):
    page_is_web = bool(getattr(self.page, 'web', False))
    port_f = tf('پورت سرویس', WEB.get('port', 8550), kb=True, width=125,
                hint='مثلاً 8550')
    status = txt('', 11, True)
    info = ft.Column(spacing=6)
    local_card = ft.Container(content=ft.Column(), padding=10, bgcolor=T()['card'],
                              border=border_all(1, T()['line']), border_radius=12)

    async def _local_copy(ev):
        u = f"http://127.0.0.1:{WEB.get('port', 8550)}/"
        ok = await _copy_text(self.page, u)
        self.toast('آدرس کپی شد' if ok else 'کپی آدرس ممکن نشد', not ok)

    def refresh_info():
        info.controls.clear()
        local_card.content = ft.Column([
            txt('آدرس لوکال‌هاست این دستگاه', 11, True, T()['primary']),
            ft.Row([
                txt(f"http://127.0.0.1:{WEB.get('port', 8550)}/", 13, True,
                    T()['primary'], expand=True, selectable=True),
                iconbtn(_ic('CONTENT_COPY'),
                        _local_copy,
                        T()['accent'], 18, 'کپی آدرس لوکال')
            ], spacing=5),
            txt('این آدرس فقط روی همان گوشی/رایانه باز می‌شود؛ سرویس باید روشن باشد.',
                9, color=T()['muted']),
        ], spacing=5)
        if web_share_active():
            status.value = f"🟢 فعال روی پورت {WEB.get('port', 8550)}"
            status.color = T()['success']
            ips = _lan_ips()
            if ips:
                info.controls.append(txt('آدرس‌های شبکه محلی برای دستگاه‌های دیگر', 11, True))
                for ip in ips:
                    url = f"http://{ip}:{WEB['port']}/"
                    async def cp(ev, u=url):
                        ok = await _copy_text(self.page, u)
                        self.toast('آدرس شبکه کپی شد' if ok else 'کپی آدرس ممکن نشد', not ok)
                    info.controls.append(card(ft.Row([
                        txt(url, 12, True, T()['primary'], expand=True, selectable=True),
                        iconbtn(_ic('CONTENT_COPY'), cp, T()['accent'], 18, 'کپی آدرس')
                    ], spacing=6), padding=8))
            else:
                info.controls.append(txt('IP شبکه تشخیص داده نشد؛ آدرس 127.0.0.1 فقط روی همین دستگاه معتبر است.',
                                         10, color=T()['warning']))
        else:
            status.value = '⚪ سرویس اشتراک خاموش است'
            status.color = T()['muted']
            info.controls.append(txt('پس از روشن‌کردن سرویس، آدرس‌های شبکه در همین بخش ظاهر می‌شوند.',
                                     10, color=T()['muted']))
        try:
            local_card.update()
            info.update()
            status.update()
        except Exception:
            pass

    def on_toggle(e):
        if e.control.value:
            wanted = port_f.value or WEB.get('port', 8550)
            ok, msg = web_share_start(wanted)
            if not ok:
                e.control.value = False
                try: e.control.update()
                except Exception: pass
                self.info('راه‌اندازی لوکال‌هاست', msg)
        else:
            web_share_stop()
            if _is_android():
                self.toast('ورود نشست‌های وب جدید مسدود شد. برای آزادکردن کامل پورت، برنامه اندروید را ببندید.')
            else:
                self.toast('سرویس اشتراک‌گذاری متوقف شد.')
        refresh_info()

    sw = K(ft.Switch, label='روشن‌کردن سرویس وب', value=web_share_active(),
           active_color=T()['accent'], on_change=on_toggle)
    refresh_info()
    notes = [
        '• آدرس 127.0.0.1 فقط روی همان دستگاه کار می‌کند؛ برای دستگاه دیگر از IP شبکه استفاده کنید.',
        '• دستگاه‌های دیگر باید به همان Wi-Fi وصل باشند و فایروال رایانه اجازه دسترسی به پورت را بدهد.',
        '• این سرویس HTTP رمزگذاری‌نشده است؛ فقط در شبکه مورد اعتماد و برای افراد مورد اعتماد فعالش کنید.',
        '• با توقف در نسخه دسکتاپ، فرایند وب بسته می‌شود. نسخه اندروید ممکن است تا بسته‌شدن کامل برنامه پورت را نگه دارد.',
    ]
    if page_is_web:
        notes.insert(0, 'شما همین حالا داخل نسخه مرورگری هستید؛ آدرس بازشده فعلی، آدرس دسترسی شماست.')
    return ft.ListView([
        card(ft.Column([
            txt('🌐 لوکال‌هاست و اشتراک شبکه', 14, True),
            ft.Row([sw, port_f], spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            status,
        ], spacing=8), padding=12),
        local_card,
        info,
        card(ft.Column([txt(n, 10, color=T()['muted']) for n in notes], spacing=5), padding=10),
    ], spacing=8, expand=True, padding=pad_only(bottom=20))


# Clipboard helper that works with synchronous and asynchronous API generations.
def _copy_text_sync(page, value):
    try:
        fn = getattr(page, 'set_clipboard', None)
        if callable(fn):
            result = fn(value)
            if inspect.isawaitable(result):
                try:
                    loop = getattr(page, 'loop', None)
                    if loop and loop.is_running():
                        loop.call_soon_threadsafe(lambda: None)
                        return False
                except Exception:
                    pass
                return False
            return True
        return False
    except Exception:
        return False

App.v_webshare = _app_v_webshare_pro


# UI operations started by the debounce timer are marshalled back to Flet's event loop where possible.
def _enhanced_debounce(self, key, fn, delay=0.22):
    timers = self.__dict__.setdefault('_timers', {})
    old = timers.get(key)
    if old:
        try: old.cancel()
        except Exception: pass
    def dispatch():
        try:
            async def run_on_ui():
                try:
                    fn()
                except Exception:
                    log_error(traceback.format_exc())
            runner = getattr(self.page, 'run_task', None)
            if callable(runner):
                runner(run_on_ui)
            else:
                fn()
        except Exception:
            log_error(traceback.format_exc())
            try: fn()
            except Exception: log_error(traceback.format_exc())
    timer = threading.Timer(max(0.05, float(delay)), dispatch)
    timer.daemon = True
    timers[key] = timer
    timer.start()

App.debounce = _enhanced_debounce


# Clock cleanup on logout prevents updates targeting detached controls.
_APP_SHOW_LOGIN_ORIGINAL = App.show_login

def _app_show_login_cleanup(self):
    self._clock_stop = True
    timer = getattr(self, '_clock_timer', None)
    if timer is not None:
        try: timer.cancel()
        except Exception: pass
    self._clock_timer = None
    return _APP_SHOW_LOGIN_ORIGINAL(self)

App.show_login = _app_show_login_cleanup



# دسترسی سریع به مدیریت PDF/CSV از داشبورد اصلی نیز در دسترس باشد.
_APP_V_DASHBOARD_ORIGINAL = App.v_dashboard

def _app_v_dashboard_pro(self):
    view = _APP_V_DASHBOARD_ORIGINAL(self)
    try:
        for item in list(getattr(view, 'controls', []) or []):
            container = getattr(item, 'content', None)
            controls = list(getattr(container, 'controls', []) or [])
            if not controls:
                continue
            first = controls[0]
            if getattr(first, 'value', '') == '⚡ اقدامات سریع':
                container.controls.append(wide(lambda: gbtn(
                    'مرکز فایل‌ها و چاپ', _ic('FOLDER_COPY'),
                    lambda e: self.push('مرکز فایل‌ها و چاپ', self.v_storage),
                    T()['primary'], expand=True)))
                break
    except Exception:
        log_error(traceback.format_exc())
    return view

App.v_dashboard = _app_v_dashboard_pro

# Main entrypoint must stay after every override above.
if __name__ == "__main__":
    if '--web-share' in sys.argv:
        try:
            _port = int(sys.argv[sys.argv.index('--web-share') + 1])
        except Exception:
            _port = 8550
        _run_flet_web(_port)
    else:
        _safe_ft_run(main)
