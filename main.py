# -*- coding: utf-8 -*-
"""عرفان حساب 6.1 — سیستم جامع حقوق و دستمزد
سازگار با Flet 0.28.x تا 1.0 | توسعه‌دهنده: عرفان بلوچ
"""
import os, sys, csv, glob, re, shutil, sqlite3, hashlib, hmac, secrets
import subprocess, traceback, inspect, tempfile, base64, io
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
APP_TITLE = "عرفان حساب"
APP_VERSION = "6.1"
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
    out = {}
    if hasattr(ft, "InputBorder"):
        out["border"] = ft.InputBorder.OUTLINE
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

def g2j(gy, gm, gd):
    g_d_m = [0,31,59,90,120,151,181,212,243,273,304,334]
    if gy > 1600: jy = 979; gy -= 1600
    else: jy = 0; gy -= 621
    gy2 = gy + 1 if gm > 2 else gy
    days = 365*gy + (gy2+3)//4 - (gy2+99)//100 + (gy2+399)//400 - 80 + gd + g_d_m[gm-1]
    jy += 33*(days//12053); days %= 12053
    jy += 4*(days//1461); days %= 1461
    if days > 365:
        jy += (days-1)//365; days = (days-1) % 365
    if days < 186: jm = 1 + days//31; jd = 1 + days%31
    else: jm = 7 + (days-186)//30; jd = 1 + (days-186)%30
    return jy, jm, jd

def today_jalali():
    n = datetime.now()
    return g2j(n.year, n.month, n.day)

def jalali_leap(y): return (y % 33) in (1, 5, 9, 13, 17, 22, 26, 30)

def days_in_month(year, month):
    if 1 <= month <= 6: return 31
    if 7 <= month <= 11: return 30
    return 30 if jalali_leap(year) else 29

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
    cands = [os.environ.get("FLET_APP_STORAGE_DATA"),
             os.path.join(os.path.expanduser("~"), ".erfanhesab"),
             os.path.join(tempfile.gettempdir(), "erfanhesab")]
    for p in cands:
        if not p: continue
        try:
            os.makedirs(p, exist_ok=True)
            probe = os.path.join(p, ".probe")
            with open(probe, "w") as f: f.write("1")
            os.remove(probe)
            return p
        except Exception: continue
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
    due_year INTEGER, due_month INTEGER, amount REAL, is_paid INTEGER DEFAULT 0,
    FOREIGN KEY(loan_id) REFERENCES loans(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS bonuses (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, emp_id INTEGER, year INTEGER, month INTEGER,
    amount INTEGER, reason TEXT, taxable INTEGER DEFAULT 1, insurable INTEGER DEFAULT 1,
    FOREIGN KEY(company_id) REFERENCES companies(id) ON DELETE CASCADE,
    FOREIGN KEY(emp_id) REFERENCES employees(id) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS deductions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    company_id INTEGER, emp_id INTEGER, year INTEGER, month INTEGER,
    amount INTEGER, reason TEXT,
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
                  ('photo','TEXT'),('notes','TEXT'),('created_at','TEXT')],
    'rate_years': [('holiday_coeff','REAL DEFAULT 1.4')],
    'benefits': [('monthly','INTEGER DEFAULT 1'),
                 ('calc_type',"TEXT DEFAULT 'fixed'")],
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
                    ('notes','TEXT')],
    'loans': [('purpose','TEXT')],
    'bonuses': [('reason','TEXT'),('taxable','INTEGER DEFAULT 1'),
                ('insurable','INTEGER DEFAULT 1')],
    'payrolls': [('holiday_amount','INTEGER DEFAULT 0'),
                 ('holiday_hours','REAL DEFAULT 0'),
                 ('bonus_amount','INTEGER DEFAULT 0'),
                 ('deduction_amount','INTEGER DEFAULT 0'),
                 ('benefits_sum','INTEGER DEFAULT 0'),
                 ('base_year_amount','INTEGER DEFAULT 0'),
                 ('deduction_amount','INTEGER DEFAULT 0')],
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
            overtime_minutes, night_minutes, absent_minutes, notes)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
            ON CONFLICT(company_id, emp_id, year, month) DO UPDATE SET
            work_days=excluded.work_days, overtime_hours=excluded.overtime_hours,
            night_hours=excluded.night_hours, absent_hours=excluded.absent_hours,
            mission_days=excluded.mission_days, shift_percent=excluded.shift_percent,
            friday_hours=excluded.friday_hours, holiday_hours=excluded.holiday_hours,
            overtime_minutes=excluded.overtime_minutes, night_minutes=excluded.night_minutes,
            absent_minutes=excluded.absent_minutes, notes=excluded.notes""",
            (cid, a['emp_id'], a['year'], a['month'],
             a.get('work_days', 0), a.get('overtime_hours', 0), a.get('night_hours', 0),
             a.get('absent_hours', 0), a.get('mission_days', 0),
             a.get('shift_percent', 0), a.get('friday_hours', 0), a.get('holiday_hours', 0),
             a.get('overtime_minutes', 0), a.get('night_minutes', 0),
             a.get('absent_minutes', 0), a.get('notes', '')))

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
                c.execute("INSERT INTO loan_installments (loan_id, installment_no, due_year, due_month, amount, is_paid) VALUES (?,?,?,?,?,0)",
                          (lid, i + 1, dy, dm, amt))
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
        shutil.copy2(self.path, self.path + ".before_restore")
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
        return self.daily_fixed(emp) / STD['hours_per_day']

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
        if ch > 0: add('حق اولاد', ch, True, False)

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
    return min(sum(a.get('work_days', 0) or 0 for a in company.get('attendances', [])
                   if a['emp_id'] == emp['id'] and a['year'] == year), 365)

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

    def _reverse_and_delete(self, c, cid, year, month):
        old = c.execute("SELECT id, emp_id, loan_install FROM payrolls WHERE company_id=? AND year=? AND month=?",
                        (cid, year, month)).fetchall()
        for p in old:
            if (p['loan_install'] or 0) > 0:
                for r in c.execute("""SELECT li.id, li.amount, li.loan_id FROM loan_installments li
                    JOIN loans l ON l.id=li.loan_id
                    WHERE l.company_id=? AND l.emp_id=? AND li.due_year=? AND li.due_month=? AND li.is_paid=1""",
                    (cid, p['emp_id'], year, month)).fetchall():
                    c.execute("UPDATE loan_installments SET is_paid=0 WHERE id=?", (r['id'],))
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

    def calculate(self, cid, year, month):
        with self.db.tx() as c:
            self._reverse_and_delete(c, cid, year, month)
            company = self.db.company_data(cid, conn=c)
            calc = PayrollCalculator(company, year, month)
            atts = {a['emp_id']: a for a in company['attendances']
                    if a['year'] == year and a['month'] == month}
            count = 0
            for emp in company['employees']:
                if not emp['is_active'] or emp['id'] not in atts: continue
                r = calc.compute_salary(emp, atts[emp['id']], company['loan_installments'],
                                        company['bonuses'], company.get('deductions', []))
                pid = c.execute("""INSERT INTO payrolls (
                    company_id, year, month, emp_id, dept_id, daily_salary, work_days,
                    base_salary_monthly, overtime_amount, night_amount, shift_amount,
                    friday_amount, holiday_amount, mission_amount, absent_ded,
                    benefits_sum, base_year_amount, bonus_amount, deduction_amount,
                    gross_salary, net_salary, insurance_emp, insurance_er, tax,
                    loan_install, overtime_hours, night_hours, absent_hours,
                    mission_days, friday_hours, holiday_hours)
                    VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                    (cid, year, month, emp['id'], emp.get('dept_id'), emp.get('daily_salary'),
                     r['work_days'], r['base_salary_monthly'], r['overtime'], r['night'],
                     r['shift'], r['friday_work'], r['holiday_work'], r['mission'],
                     r['absent_ded'], sum(x['amount'] for x in r['benefits_list'] if x['amount'] > 0),
                     r['base_year_amount'], r['bonus_amount'], r['deduction_amount'],
                     r['gross'], r['net'], r['insurance_emp'], r['insurance_er'], r['tax'],
                     r['loan_install'], r['overtime_hours'], r['night_hours'], r['absent_hours'],
                     r['mission_days'], r['friday_hours'], r['holiday_hours'])).lastrowid
                det = [(b['name'], b['amount'], 1 if b['amount'] >= 0 else 2)
                       for b in r['benefits_list']]
                det += [('بیمه سهم کارگر', r['insurance_emp'], 2),
                        ('مالیات حقوق', r['tax'], 2),
                        ('کسر کار', r['absent_ded'], 2)]
                if r['loan_install']: det.append(('قسط وام', r['loan_install'], 2))
                for n, a, t in det:
                    c.execute("INSERT INTO payroll_details (payroll_id, name, amount, type) VALUES (?,?,?,?)",
                              (pid, n, a, t))
                for e in accounting_entries(pid, year, month, emp, r):
                    c.execute("""INSERT INTO accounting_entries
                        (company_id, payroll_id, entry_date, account_code, account_name,
                         debit, credit, description) VALUES (?,?,?,?,?,?,?,?)""",
                        (cid, pid, e['entry_date'], e['account_code'], e['account_name'],
                         e['debit'], e['credit'], e['description']))
                for iid in r['loan_inst_ids']:
                    inst = c.execute("SELECT amount, loan_id FROM loan_installments WHERE id=?", (iid,)).fetchone()
                    c.execute("UPDATE loan_installments SET is_paid=1 WHERE id=?", (iid,))
                    c.execute("UPDATE loans SET remaining_balance=MAX(remaining_balance-?,0) WHERE id=?",
                              (rnd(inst['amount']), inst['loan_id']))
                    left = c.execute("SELECT COUNT(*) FROM loan_installments WHERE loan_id=? AND is_paid=0",
                                     (inst['loan_id'],)).fetchone()[0]
                    if left == 0:
                        c.execute("UPDATE loans SET status=1, remaining_balance=0 WHERE id=?", (inst['loan_id'],))
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
                monthly = ((emp.get('daily_salary') or 0) * 30)
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
    path = os.path.join(export_dir(), f"payroll_full_{year}_{month:02d}.csv")
    write_csv(path, header, rows)
    return path

def export_attendance_csv(db, cid, year, month, employees, att_map):
    rows = []
    for i, e in enumerate(employees, 1):
        a = att_map.get(e['id'], {})
        rows.append([i, e['id'], e.get('first_name',''), e.get('last_name',''),
                     e.get('national_code',''), a.get('work_days',0),
                     hours_to_hm(a.get('overtime_hours',0)),
                     hours_to_hm(a.get('night_hours',0)),
                     hours_to_hm(a.get('absent_hours',0)),
                     a.get('mission_days',0), a.get('shift_percent',0),
                     a.get('friday_hours',0), a.get('holiday_hours',0)])
    path = os.path.join(export_dir(), f"timesheet_{year}_{month:02d}.csv")
    write_csv(path, ['ردیف','کد','نام','فامیل','کد ملی','روز','اضافه','شب','کسر',
                     'مأموریت','نوبت%','جمعه','تعطیل'], rows)
    return path

# ═══════════════════════ PDF ═══════════════════════
_MIRROR = str.maketrans("()[]{}<>", ")(][}{><")
_LTR_RUN = re.compile(r'[0-9A-Za-z][0-9A-Za-z.,:/%\-_]*')

def _simple_bidi(s):
    return _LTR_RUN.sub(lambda m: m.group(0)[::-1], s[::-1]).translate(_MIRROR)

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
    pdf, _ = _pdf_init((297, 210))
    W, M = 297, 6
    pdf.add_page()
    pdf.set_fill_color(30, 58, 95); pdf.rect(M, 6, W - 2*M, 12, 'F')
    pdf.set_xy(M, 8); pdf.set_font("F", size=13); pdf.set_text_color(240, 180, 41)
    pdf.cell(W - 2*M, 8, rtl(f"لیست حقوق و دستمزد — {MONTHS[month-1]} {year}"), border=0, align='C')
    pdf.set_xy(M, 20); pdf.set_font("F", size=9); pdf.set_text_color(0, 0, 0)
    pdf.cell(W - 2*M, 6, rtl(f"شرکت: {company.get('name','')}"), border=0, align='R')
    y = 28
    headers = ["#", "نام", "پایه", "اضافه", "شب", "نوبت", "جمعه", "مزایا",
               "ناخالص", "بیمه", "مالیات", "وام", "کسر", "خالص"]
    col_w = [(W - 2*M) / len(headers)] * len(headers)
    pdf.set_fill_color(240, 180, 41); pdf.set_text_color(30, 58, 95); pdf.set_font("F", size=8)
    x = M
    for i, h in enumerate(headers):
        pdf.set_xy(x, y); pdf.cell(col_w[i], 6, rtl(h), border=1, align='C', fill=True)
        x += col_w[i]
    y += 6
    pdf.set_text_color(0, 0, 0); pdf.set_font("F", size=7)
    total_gross = total_net = 0
    for idx, r in enumerate(rows, 1):
        if y > 190: pdf.add_page(); y = 20
        vals = [str(idx), f"{r['first_name']} {r['last_name']}",
                fmt(r['base_salary_monthly']), fmt(r.get('overtime_amount', 0)),
                fmt(r.get('night_amount', 0)), fmt(r.get('shift_amount', 0)),
                fmt(r.get('friday_amount', 0)), fmt(r.get('benefits_sum', 0)),
                fmt(r['gross_salary']), fmt(r['insurance_emp']), fmt(r['tax']),
                fmt(r['loan_install']), fmt(r['absent_ded']), fmt(r['net_salary'])]
        x = M
        for i, v in enumerate(vals):
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
    cls = getattr(ft, cls_name, None) or getattr(ft, "Button", None) or ft.ElevatedButton
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
        self.apply_theme()
        self.show_login()

    def apply_theme(self):
        self.page.theme_mode = ft.ThemeMode.DARK if STATE['dark'] else ft.ThemeMode.LIGHT
        self.page.bgcolor = T()['bg']
        if self.body is not None: self.body.bgcolor = T()['bg']

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
            if check_pw(pw.value or "", stored):
                if not (stored or '').startswith("pbkdf2$"):
                    self.db.x("UPDATE companies SET admin_password=? WHERE id=?",
                              (hash_pw(pw.value), self.cid))
                self.build_shell()
            else:
                err.value = "رمز اشتباه است"; pw.value = ""; p.update()
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
        self.appbar = K(ft.AppBar,
                        title=ft.Text(APP_TITLE, color=T()['accent'],
                                      weight=ft.FontWeight.BOLD, size=15),
                        center_title=True, bgcolor=T()['primary'], toolbar_height=52,
                        actions=[iconbtn(_ic("PALETTE"), self.theme_picker, T()['accent'], 20, "تغییر تم"),
                                 iconbtn(_ic("DARK_MODE", "BRIGHTNESS_6"), self.toggle_theme,
                                         T()['accent'], 20, "شب/روز")])
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
        p.add(self.body)
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
        title, builder = self.stack[-1]
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
        h = min((self.page.height or 700) * 0.65, 640)
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
            gradient=ft.LinearGradient(begin=ft.Alignment(-1, -1), end=ft.Alignment(1, 1),
                                       colors=T()['grad']),
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
            dict(key='national_code', label='کد ملی (۱۰ رقم)', kb=True, required=True),
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
        depts = self.db.q("SELECT * FROM departments WHERE company_id=?", (self.cid,))
        init = dict(emp) if emp else dict(
            is_active=1, marital=0, child_count=0,
            employment_date=jalali_today_str(), contract_type='رسمی',
            dept_id=depts[0]['id'] if depts else None)
        init['base_hours'] = (emp or {}).get('base_hours') or 0

        def save(v):
            if not (v['national_code'].isdigit() and len(v['national_code']) == 10):
                return "کد ملی باید ۱۰ رقم عددی باشد"
            if (v['daily_salary'] or 0) <= 0:
                return "حقوق روزانه معتبر نیست"
            for key, lbl in (('employment_date', 'تاریخ استخدام'),
                             ('birth_date', 'تاریخ تولد'), ('contract_end', 'پایان قرارداد')):
                d = norm(v.get(key) or '')
                if d:
                    ok, msg = validate_jalali(d)
                    if not ok: return f"{lbl}: {msg}"
                    v[key] = d.replace('-', '/')
            v['base_hours'] = v['base_hours'] or None
            v['iban'] = (v['iban'] or '').upper().replace(' ', '')
            if not v.get('created_at'): v['created_at'] = jalali_today_str()
            try:
                if emp: self.db.update('employees', emp['id'], v)
                else: self.db.insert('employees', dict(v, company_id=self.cid))
            except sqlite3.IntegrityError:
                return "این کد ملی قبلاً ثبت شده است"
            self.toast("✅ ذخیره شد"); return None

        def delete():
            self.db.delete('employees', emp['id'])
            self.toast("حذف شد"); self.refresh()
        self.form("✏️ ویرایش پرسنل" if emp else "➕ پرسنل جدید",
                  self.emp_spec(depts), init, save,
                  (lambda: self.confirm("با حذف، تمام سوابق حذف می‌شوند. ادامه؟",
                                        delete, "حذف پرسنل")) if emp else None)

    def emp_detail(self, emp):
        depts = {d['id']: d for d in self.db.q("SELECT * FROM departments WHERE company_id=?", (self.cid,))}
        dept = depts.get(emp.get('dept_id'))
        photo_widget = None
        photo_b64 = emp.get('photo') or ''
        if photo_b64:
            try:
                src = photo_b64 if photo_b64.startswith('data:') else f"data:image/png;base64,{photo_b64}"
                photo_widget = ft.Container(ft.Image(src=src, width=90, height=90,
                                                     fit="cover", border_radius=45),
                                            width=100, height=100, alignment=center())
            except Exception: photo_widget = None
        if not photo_widget:
            initials = (emp.get('first_name') or '?')[:1] + (emp.get('last_name') or '')[:1]
            photo_widget = ft.Container(
                ft.Text(initials, size=28, weight=ft.FontWeight.BOLD, color=T()['primary']),
                width=100, height=100, bgcolor=T()['accent'], border_radius=50, alignment=center())

        def up_photo(e): self._pick_photo(emp['id'])

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
            self.close_dlg(dlg); self.contract_view(emp)

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

    def _pick_photo(self, emp_id):
        try:
            fp = K(ft.FilePicker, on_result=lambda e: self._on_photo_picked(e, emp_id))
            self.page.overlay.append(fp)
            self.page.update()
            try: fp.pick_files(allow_multiple=False, allowed_extensions=["jpg","jpeg","png","webp"])
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
        c = self.db.company_data(self.cid)
        depts = {d['id']: d for d in c['departments']}
        state = {'q': '', 'dept': '', 'status': 'active', 'sort': 'name'}
        holder = ft.Column(spacing=4, scroll=ft.ScrollMode.AUTO, expand=True)
        count_holder = ft.Container()

        def row_for(emp):
            avatar = None
            if emp.get('photo'):
                try:
                    src = emp['photo']
                    if not src.startswith('data:'): src = f"data:image/png;base64,{src}"
                    avatar = ft.Container(ft.Image(src=src, width=48, height=48, fit="cover",
                                                    border_radius=24), width=48, height=48)
                except Exception: avatar = None
            if not avatar:
                ini = (emp.get('first_name') or '?')[:1] + (emp.get('last_name') or '')[:1]
                avatar = ft.Container(
                    ft.Text(ini, size=15, weight=ft.FontWeight.BOLD, color=T()['primary']),
                    width=48, height=48, bgcolor=T()['accent'], border_radius=24, alignment=center())

            dept_name = (depts.get(emp.get('dept_id')) or {}).get('title', '-')
            return ft.Container(
                content=ft.Row([
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
                if q and q not in full: continue
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
            for emp in vis: holder.controls.append(row_for(emp))
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
                tf('جستجو...', on_change=lambda e: (state.update({'q': e.control.value or ''}), fill()),
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

    # ── کارکرد (جدول مکانیزه) ──
    def v_attendance(self):
        c = self.db.company_data(self.cid)
        employees = [e for e in c['employees'] if e.get('is_active')]
        rates = self.db.q("SELECT * FROM rate_years WHERE company_id=? AND year<=? ORDER BY year DESC LIMIT 1",
                          (self.cid, self.year))
        shift_def = rates[0]['shift_percent'] if rates else 15
        att_map = {a['emp_id']: a for a in c['attendances']
                   if a['year'] == self.year and a['month'] == self.month}
        state = {'q': '', 'dept': ''}
        inputs = {}
        holder = ft.Column(spacing=2, scroll=ft.ScrollMode.AUTO, expand=True)
        summary_holder = ft.Container()

        FIELDS = ('work_days','overtime_hours','overtime_minutes','night_hours','night_minutes',
                  'absent_hours','absent_minutes','mission_days','shift_percent',
                  'friday_hours','holiday_hours')

        COLS = [('work_days','روز',50), ('overtime_hours','اضافه س',52),
                ('overtime_minutes','اضافه د',52), ('night_hours','شب س',50),
                ('night_minutes','شب د',50), ('absent_hours','کسر س',50),
                ('absent_minutes','کسر د',50), ('mission_days','مأموریت',58),
                ('shift_percent','نوبت٪',56), ('friday_hours','جمعه',50),
                ('holiday_hours','تعطیل',50)]
        NAME_W = 130

        def num_input(emp, fname, value, hint=''):
            key = (emp['id'], fname)
            raw = inputs.get(key, "" if value in (None, 0) else
                             (f"{value:g}" if isinstance(value, float) else str(value)))
            def on_change(e): inputs[key] = e.control.value
            return K(ft.TextField, value=raw, dense=True, text_size=11,
                     text_align=ft.TextAlign.CENTER, hint_text=hint,
                     keyboard_type=ft.KeyboardType.NUMBER,
                     content_padding=pad_sym(2, 4), bgcolor=T()['card'],
                     on_change=on_change, **_border_kwargs(6))

        def build_header_row():
            cells = [ft.Container(content=txt('کارمند', 10, True, '#ffffff'),
                                  width=NAME_W, padding=pad_sym(4, 8),
                                  alignment=ft.Alignment(-1, 0))]
            for _, lbl, w in COLS:
                cells.append(ft.Container(content=txt(lbl, 9, True, '#ffffff'),
                                          width=w, padding=pad_sym(2, 8), alignment=center()))
            return ft.Container(content=ft.Row(cells, spacing=2, scroll=ft.ScrollMode.AUTO),
                                bgcolor=T()['primary'], padding=pad_sym(4, 0))

        def build_emp_row(idx, emp, att):
            def gv(key, default=0):
                return att[key] if key in att and att[key] is not None else default
            is_even = (idx % 2 == 0)
            row_bg = T()['card'] if is_even else alpha(T()['primary'], 0x10)
            border_col = T()['line'] if is_even else alpha(T()['primary'], 0x25)
            has_data = emp['id'] in att_map
            avatar = ft.Container(
                ft.Text((emp.get('first_name') or '?')[:1], size=12,
                        weight=ft.FontWeight.BOLD, color=T()['primary']),
                width=30, height=30,
                bgcolor=T()['accent'] if has_data else alpha(T()['accent'], 0x55),
                border_radius=15, alignment=center())
            name_cell = ft.Container(
                content=ft.Row([
                    avatar,
                    ft.Column([
                        txt(f"{emp.get('first_name','')} {emp.get('last_name','')}",
                            10, True, no_wrap=True, overflow=ft.TextOverflow.ELLIPSIS),
                        txt(f"#{emp.get('personnel_code') or emp['id']}", 8, color=T()['muted']),
                    ], spacing=0, expand=True),
                ], spacing=6, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                width=NAME_W, padding=pad_sym(4, 3))
            num_cells = []
            for fname, _, w in COLS:
                num_cells.append(ft.Container(
                    num_input(emp, fname, gv(fname, shift_def if fname == 'shift_percent' else 0)),
                    width=w, padding=pad_sym(1, 0)))
            return ft.Container(content=ft.Row([name_cell] + num_cells, spacing=2,
                                                scroll=ft.ScrollMode.AUTO),
                                bgcolor=row_bg, border=border_all(1, border_col),
                                border_radius=8, padding=pad_sym(3, 3))

        def rebuild(e=None):
            holder.controls.clear()
            q = (state['q'] or '').strip().lower()
            shown = []
            for emp in employees:
                full = (f"{emp.get('first_name','')} {emp.get('last_name','')} "
                        f"{emp.get('national_code','')} {emp['id']} {emp.get('mobile','')}").lower()
                if q and q not in full: continue
                if state['dept'] and str(emp.get('dept_id') or '') != str(state['dept']): continue
                shown.append(emp)
            holder.controls.append(build_header_row())
            for idx, emp in enumerate(shown):
                holder.controls.append(build_emp_row(idx, emp, att_map.get(emp['id'], {})))
            if not shown: holder.controls.append(self.empty("پرسنل فعالی یافت نشد", _ic('PEOPLE_OUTLINE')))
            holder.controls.append(ft.Container(height=20))
            registered = sum(1 for emp in shown if emp['id'] in att_map)
            summary_holder.content = ft.Row([
                badge(f"کل: {len(shown)}", T()['primary'], '#ffffff', 9),
                badge(f"ثبت‌شده: {registered}", '#dbeafe', '#1d4ed8', 9),
                badge(f"باقی‌مانده: {len(shown) - registered}", '#fef3c7', '#92400e', 9),
                badge(f"{MONTHS[self.month - 1]} {self.year}", T()['accent'], T()['primary'], 9),
            ], spacing=6, wrap=True)
            try: holder.update(); summary_holder.update()
            except Exception: pass

        def save_all(e=None):
            dim = days_in_month(self.year, self.month)
            errors, staged = [], []
            for emp in employees:
                touched = any((emp['id'], f) in inputs for f in FIELDS)
                if emp['id'] not in att_map and not touched: continue
                def n(fname, default=0, emp=emp):
                    key = (emp['id'], fname)
                    if key in inputs: return parse_float(inputs[key])
                    return parse_float(att_map.get(emp['id'], {}).get(fname, default))
                work = n('work_days')
                ot_h = n('overtime_hours'); ot_m = n('overtime_minutes')
                ng_h = n('night_hours'); ng_m = n('night_minutes')
                ab_h = n('absent_hours'); ab_m = n('absent_minutes')
                mission = n('mission_days'); shift = n('shift_percent', shift_def)
                friday = n('friday_hours'); holiday = n('holiday_hours')
                label = f"{emp.get('first_name','')} {emp.get('last_name','')}"
                if work < 0 or work > dim:
                    errors.append(f"{label}: روز کارکرد ۰ تا {dim}"); continue
                if not (0 <= ot_m <= 59 and 0 <= ng_m <= 59 and 0 <= ab_m <= 59):
                    errors.append(f"{label}: دقیقه باید ۰ تا ۵۹"); continue
                if min(ot_h, ng_h, ab_h, mission, shift, friday, holiday) < 0:
                    errors.append(f"{label}: مقدار منفی مجاز نیست"); continue
                if mission > dim or shift > 100:
                    errors.append(f"{label}: مقدار خارج از محدوده"); continue
                staged.append(dict(emp_id=emp['id'], year=self.year, month=self.month,
                                   work_days=work, overtime_hours=ot_h, overtime_minutes=ot_m,
                                   night_hours=ng_h, night_minutes=ng_m,
                                   absent_hours=ab_h, absent_minutes=ab_m,
                                   mission_days=mission, shift_percent=shift,
                                   friday_hours=friday, holiday_hours=holiday))
            if errors:
                self.info('بررسی', 'ذخیره نشد:\n\n' + '\n'.join(errors[:15])); return
            for rec in staged: self.db.upsert_attendance(self.cid, rec)
            inputs.clear()
            self.toast(f'✅ {len(staged)} رکورد ذخیره شد.')
            self.refresh()

        def copy_prev(e=None):
            py, pm = (self.year, self.month - 1) if self.month > 1 else (self.year - 1, 12)
            ids = {emp['id'] for emp in employees}
            prev = [a for a in c['attendances']
                    if a['year'] == py and a['month'] == pm and a['emp_id'] in ids]
            if not prev:
                self.toast('ماه قبل اطلاعاتی ندارد.', True); return
            def go():
                for a in prev:
                    self.db.upsert_attendance(self.cid, dict(a, year=self.year, month=self.month))
                inputs.clear()
                self.toast(f'✅ {len(prev)} رکورد کپی شد.'); self.refresh()
            self.confirm(f'کارکرد {len(prev)} نفر از ماه قبل کپی شود؟', go, 'کپی', False)

        def clear_month(e=None):
            def go():
                with self.db.tx() as conn:
                    conn.execute("DELETE FROM attendances WHERE company_id=? AND year=? AND month=?",
                                 (self.cid, self.year, self.month))
                inputs.clear()
                self.toast('🗑 کارکرد ماه پاک شد'); self.refresh()
            self.confirm(f"همه کارکرد {MONTHS[self.month-1]} {self.year} پاک شود؟", go, 'حذف')

        def export_sheet(e=None):
            try:
                path = export_attendance_csv(self.db, self.cid, self.year, self.month,
                                             employees, att_map)
                self.file_dialog(path, "✅ CSV کارکرد ساخته شد")
            except Exception as ex: self.info("خطا", str(ex))

        def fill_all(e=None):
            dim = days_in_month(self.year, self.month)
            for emp in employees:
                inputs[(emp['id'], 'work_days')] = str(dim)
            rebuild()
            self.toast(f"✅ {dim} روز برای همه پر شد (ذخیره را بزنید)")

        rebuild()
        return ft.Column([
            card(ft.Column([self.period_bar(self.refresh), summary_holder], spacing=6), padding=10),
            card(ft.Column([
                tf("🔍 جستجو", on_change=lambda e: (state.update({'q': e.control.value or ''}), rebuild()),
                   prefix=_ic('SEARCH'), size=12),
                dd('فیلتر دپارتمان',
                   [('', 'همه دپارتمان‌ها')] + [(d['id'], d['title']) for d in c['departments']],
                   '', lambda e: (state.update({'dept': e.control.value or ''}), rebuild()), size=11),
                ft.Row([
                    gbtn('💾 ذخیره همه', _ic('SAVE'), save_all, '#047857', expand=True),
                    obtn('⚡ پرکردن روزها', _ic('BOLT'), fill_all, expand=True),
                ], spacing=6),
                ft.Row([
                    obtn('📋 کپی ماه قبل', _ic('CONTENT_COPY'), copy_prev, expand=True),
                    obtn('📥 CSV', _ic('DOWNLOAD'), export_sheet, expand=True),
                    iconbtn(_ic('DELETE'), clear_month, '#c0392b', 22, 'حذف کارکرد ماه'),
                ], spacing=6),
            ], spacing=6), padding=10),
            holder,
        ], expand=True, spacing=6)

    # ── حقوق ──
    def v_payroll(self):
        c = self.db.company_data(self.cid)
        emps = {e['id']: e for e in c['employees']}
        depts = {d['id']: d for d in c['departments']}
        pays_all = self.svc.payrolls(self.cid, self.year, self.month)
        st = {'q': '', 'dept': ''}
        holder = ft.Column(spacing=4, scroll=ft.ScrollMode.AUTO, expand=True)
        totals_holder = ft.Container()

        def filtered():
            out = []
            for p in pays_all:
                e = emps.get(p['emp_id'])
                if not e: continue
                hay = (f"{e.get('first_name','')} {e.get('last_name','')} "
                       f"{e.get('national_code','')} {e['id']} {e.get('personnel_code','')}").lower()
                if st['q'] and st['q'] not in hay: continue
                if st['dept'] and str(e.get('dept_id') or '') != str(st['dept']): continue
                out.append(p)
            return out

        def fill():
            holder.controls.clear()
            ps = filtered()
            gross = sum(p['gross_salary'] for p in ps)
            net = sum(p['net_salary'] for p in ps)
            totals_holder.content = card(ft.Row([
                ft.Column([txt("تعداد", 9, color=T()['muted']), txt(str(len(ps)), 12, True)], spacing=0),
                ft.Column([txt("ناخالص", 9, color=T()['muted']), txt(fmt(gross), 12, True)], spacing=0),
                ft.Column([txt("خالص", 9, color=T()['muted']),
                           txt(fmt(net), 12, True, T()['success'])], spacing=0),
            ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN), padding=10)
            for i, p in enumerate(ps, 1):
                e = emps.get(p['emp_id']) or {}
                dept_name = (depts.get(e.get('dept_id')) or {}).get('title', '-')
                holder.controls.append(ft.Container(
                    content=ft.Column([
                        ft.Row([
                            badge(f"#{i}", T()['primary'], '#ffffff', 9),
                            txt(f"{e.get('first_name','')} {e.get('last_name','')}",
                                12, True, expand=True, no_wrap=True,
                                overflow=ft.TextOverflow.ELLIPSIS),
                            badge(f"روز: {p['work_days']:g}", T()['accent'], T()['primary'], 9),
                        ], spacing=4),
                        txt(f"{dept_name} • {e.get('job_title','')}",
                            10, color=T()['muted'], no_wrap=True, overflow=ft.TextOverflow.ELLIPSIS),
                        ft.Row([
                            txt(f"پایه: {fmt(p['base_salary_monthly'])}", 10, color=T()['muted']),
                            txt(f"اضافه: {fmt(p.get('overtime_amount',0))}", 10, color=T()['muted']),
                            txt(f"مزایا: {fmt(p.get('benefits_sum',0))}", 10, color=T()['muted']),
                        ], spacing=6, wrap=True),
                        ft.Row([
                            txt(f"بیمه: {fmt(p['insurance_emp'])}", 10, color=T()['muted']),
                            txt(f"مالیات: {fmt(p['tax'])}", 10, color=T()['muted']),
                            txt(f"خالص: {fmt(p['net_salary'])}", 11, True, T()['success']),
                        ], spacing=6, wrap=True),
                    ], spacing=3),
                    padding=pad_sym(10, 6), bgcolor=T()['card'], border_radius=10,
                    border=border_all(1, T()['line']),
                    on_click=lambda ev, pid=p['id']: self.push("فیش حقوقی", lambda: self.v_slip(pid))))
            if not ps:
                holder.controls.append(self.empty(
                    "برای این ماه فیشی نیست؛ کارکرد را ثبت و «محاسبه» را بزنید", _ic("RECEIPT_LONG")))
            holder.controls.append(ft.Container(height=20))
            try: holder.update(); totals_holder.update()
            except Exception: pass

        def calc(e):
            def go():
                try: n = self.svc.calculate(self.cid, self.year, self.month)
                except Exception as ex:
                    log_error(traceback.format_exc()); self.toast(f"خطا: {ex}", True); return
                self.toast("کارکردی ثبت نشده است" if n == 0 else f"✅ {n} فیش محاسبه شد", n == 0)
                self.refresh()
            if pays_all:
                self.confirm("فیش‌های قبلی بازمحاسبه می‌شوند. ادامه؟", go, "بازمحاسبه", False)
            else: go()

        def delete_month(e):
            if not pays_all:
                self.toast("فیشی برای حذف نیست", True); return
            def go():
                n = self.svc.delete_month(self.cid, self.year, self.month)
                self.toast(f"🗑 {n} فیش حذف شد"); self.refresh()
            self.confirm(f"همه‌ی فیش‌های {MONTHS[self.month - 1]} {self.year} حذف شود؟", go, "حذف فیش‌ها")

        def pdf_slips(e):
            ps = filtered()
            if not ps: self.toast("فیشی وجود ندارد", True); return
            slips = []
            for p in ps:
                em = emps.get(p['emp_id'])
                if em:
                    slips.append(dict(pay=p, emp=em, dept=depts.get(em.get('dept_id')),
                                      details=self.svc.details(p['id'])))
            try:
                path = build_pdf(os.path.join(export_dir(),
                    f"payslips_{self.year}_{self.month:02d}_{datetime.now():%H%M%S}.pdf"), c, slips)
                self.file_dialog(path, "📄 PDF فیش‌ها ساخته شد", len(slips))
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا در ساخت PDF", str(ex))

        def pdf_list(e):
            ps = filtered()
            if not ps: self.toast("فیشی وجود ندارد", True); return
            rows = []
            for p in ps:
                e2 = emps.get(p['emp_id']) or {}
                rows.append(dict(first_name=e2.get('first_name',''), last_name=e2.get('last_name',''),
                                 base_salary_monthly=p['base_salary_monthly'],
                                 overtime_amount=p.get('overtime_amount',0),
                                 night_amount=p.get('night_amount',0),
                                 shift_amount=p.get('shift_amount',0),
                                 friday_amount=p.get('friday_amount',0),
                                 benefits_sum=p.get('benefits_sum',0),
                                 gross_salary=p['gross_salary'],
                                 insurance_emp=p['insurance_emp'], tax=p['tax'],
                                 loan_install=p['loan_install'], absent_ded=p['absent_ded'],
                                 net_salary=p['net_salary']))
            try:
                path = os.path.join(export_dir(), f"payroll_list_{self.year}_{self.month:02d}.pdf")
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
        return ft.Column([
            card(ft.Column([
                self.period_bar(self.refresh),
                tf("🔍 جستجو", on_change=lambda e: (st.update({'q': (e.control.value or '').lower().strip()}), fill()),
                   prefix=_ic("SEARCH"), size=12),
                dd('فیلتر دپارتمان',
                   [('', 'همه دپارتمان‌ها')] + [(d['id'], d['title']) for d in c['departments']],
                   '', lambda e: (st.update({'dept': e.control.value or ''}), fill()), size=11),
                wide(lambda: gbtn("🧮 محاسبه حقوق", _ic("CALCULATE"), calc, "#10b981", expand=True)),
                ft.Row([
                    obtn("📄 فیش‌ها PDF", _ic("PICTURE_AS_PDF"), pdf_slips, expand=True),
                    obtn("📋 لیست PDF", _ic("LIST_ALT"), pdf_list, expand=True),
                ], spacing=6),
                ft.Row([
                    obtn("📊 CSV", _ic("FILE_DOWNLOAD"), export_csv, expand=True),
                    iconbtn(_ic("DELETE"), delete_month, "#c0392b", 22, "حذف فیش‌های ماه"),
                ], spacing=6),
            ], spacing=6), padding=10),
            totals_holder, holder], expand=True, spacing=6)

    def v_slip(self, pid):
        p = self.db.q1("SELECT * FROM payrolls WHERE id=?", (pid,))
        if not p: return self.empty("فیش یافت نشد")
        c = self.db.company_data(self.cid)
        e = next((x for x in c['employees'] if x['id'] == p['emp_id']), None)
        dept = next((d for d in c['departments'] if d['id'] == (e or {}).get('dept_id')), None)
        dets = self.svc.details(pid)
        ben = [d for d in dets if d['type'] == 1]
        ded = [d for d in dets if d['type'] == 2 and d['amount']]
        extras = [(n, p[k]) for n, k in (("اضافه‌کاری", 'overtime_amount'),
                                          ("نوبت‌کاری", 'shift_amount'), ("شب‌کاری", 'night_amount'),
                                          ("ماموریت", 'mission_amount'), ("جمعه‌کاری", 'friday_amount'),
                                          ("تعطیل‌کاری", 'holiday_amount')) if p.get(k)]

        def sec(title, rows, color):
            items = [txt(title, 12, True, color)]
            for n, a in rows:
                items.append(ft.Container(
                    content=ft.Row([txt(n, 11, expand=True), txt(fmt(a), 11, True)]),
                    padding=pad_sym(8, 3), bgcolor=T()['bg'], border_radius=6))
            return card(ft.Column(items, spacing=4), padding=10)

        def pdf1(ev):
            if not e: return
            try:
                path = build_pdf(os.path.join(export_dir(),
                    f"payslip_{p['emp_id']}_{p['year']}_{p['month']:02d}.pdf"),
                    c, [dict(pay=p, emp=e, dept=dept, details=dets)])
                self.file_dialog(path, "📄 PDF ساخته شد", 1)
            except Exception as ex:
                log_error(traceback.format_exc()); self.info("خطا", str(ex))

        def col(label, val):
            return ft.Column([txt(label, 9, color=T()['muted']), txt(val, 11, True)],
                             spacing=1, expand=True)

        head = card(ft.Column([
            ft.Row([txt(f"{e.get('first_name','')} {e.get('last_name','')}" if e else '-',
                        14, True, expand=True),
                    badge(f"{(dept or {}).get('title','-')}", alpha(T()['primary'], 0x22),
                          T()['primary'], 9)]),
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
                     [('حقوق پایه', p['base_salary_monthly'])] + [(d['name'], d['amount']) for d in ben],
                     T()['primary'])]
        if extras: parts.append(sec('اضافات', extras, T()['primary']))
        if ded: parts.append(sec('کسورات', [(d['name'], d['amount']) for d in ded], T()['danger']))
        parts += [total, wide(lambda: gbtn('📄 PDF', _ic('PICTURE_AS_PDF'), pdf1,
                                           T()['primary'], expand=True))]
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
            tile(_ic("LOCK"), "تغییر رمز", "رمز ورود", lambda e: self.password_form()),
            tile(_ic("PALETTE"), "تغییر تم", "نیلی، زمرد، غروب", self.theme_picker),
            tile(_ic("DARK_MODE", "BRIGHTNESS_6"), "حالت تاریک", "روز/شب", self.toggle_theme),
            tile(_ic("LOGOUT"), "خروج", "صفحه ورود", lambda e: self.show_login()),
        ]
        items.append(card(ft.Column([
            txt(f'عرفان حساب — نسخه {APP_VERSION}', 13, True, T()['primary']),
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
        self.set_fab(_ic("PHOTO_CAMERA"), lambda e: self._pick_logo())

    def _pick_logo(self):
        try:
            fp = K(ft.FilePicker, on_result=self._on_logo_picked)
            self.page.overlay.append(fp); self.page.update()
            try: fp.pick_files(allow_multiple=False, allowed_extensions=["jpg","jpeg","png","webp","svg"])
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
            if len(v['new']) < 4: return "رمز جدید حداقل ۴ کاراکتر"
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
                    dict(key='calc_type', label='نوع محاسبه', type='dropdown',
                         options=[('fixed','مبلغ ثابت'), ('child','بر اساس فرزند'),
                                  ('marital','فقط متاهل‌ها'), ('percent','درصدی')])]
            def save(v):
                v['year'] = self.year
                if b: self.db.update('benefits', b['id'], v)
                else: self.db.insert('benefits', dict(v, company_id=self.cid))
                return None
            def delete():
                self.db.delete('benefits', b['id']); self.refresh()
            self.form("✏️ ویرایش" if b else f"➕ مزایای {self.year}", spec,
                      b or dict(taxable=1, insurable=1, calc_type='fixed'), save,
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

        def loan_form():
            spec = [dict(key='emp_id', label='پرسنل', type='dropdown', options=opts, cast=int, required=True),
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
                self.db.save_loan(self.cid, v['emp_id'], v['principal'], v['count'],
                                  v['sy'], v['sm'], v.get('purpose',''))
                self.toast("✅ وام ثبت شد"); return None
            self.form("💰 وام جدید", spec, dict(sy=self.year, sm=self.month), save)

        def bonus_form():
            spec = [dict(key='emp_id', label='پرسنل', type='dropdown', options=opts, cast=int, required=True),
                    dict(key='year', label='سال', type='int'), dict(key='month', label='ماه', type='int'),
                    dict(key='amount', label='مبلغ پاداش (ریال)', type='money', required=True),
                    dict(key='reason', label='دلیل پاداش'),
                    dict(key='taxable', label='مشمول مالیات', type='bool'),
                    dict(key='insurable', label='مشمول بیمه', type='bool')]
            def save(v):
                if not 1 <= v['month'] <= 12: return "ماه معتبر نیست"
                if not 1300 <= v['year'] <= 1500: return "سال معتبر نیست"
                self.db.insert('bonuses', dict(v, company_id=self.cid))
                self.toast("✅ پاداش ثبت شد"); return None
            self.form("🎁 پاداش جدید", spec,
                      dict(year=self.year, month=self.month, taxable=1, insurable=1), save)

        def deduction_form():
            spec = [dict(key='emp_id', label='پرسنل', type='dropdown', options=opts, cast=int, required=True),
                    dict(key='year', label='سال', type='int'), dict(key='month', label='ماه', type='int'),
                    dict(key='amount', label='مبلغ کسورات (ریال)', type='money', required=True),
                    dict(key='reason', label='دلیل کسورات')]
            def save(v):
                if not 1 <= v['month'] <= 12: return "ماه معتبر نیست"
                if not 1300 <= v['year'] <= 1500: return "سال معتبر نیست"
                self.db.insert('deductions', dict(v, company_id=self.cid))
                self.toast("✅ کسورات ثبت شد"); return None
            self.form("➖ کسورات جدید", spec, dict(year=self.year, month=self.month), save)

        def loan_detail(l, e):
            insts = self.db.q("SELECT * FROM loan_installments WHERE loan_id=? ORDER BY installment_no", (l['id'],))
            paid = sum(1 for i in insts if i['is_paid'])
            lines = [f"{i['installment_no']}) {i['due_year']}/{i['due_month']:02d} — "
                     f"{fmt(i['amount'])} — {'✅ کسر شده' if i['is_paid'] else '⏳ در انتظار'}" for i in insts]
            def delete():
                self.db.delete('loans', l['id'])
                self.toast("وام حذف شد"); self.refresh()
            d = ft.AlertDialog(
                title=ft.Text(f"وام {e.get('first_name','')} {e.get('last_name','')}", size=13),
                content=ft.Container(ft.Column([
                    txt(f"اصل: {fmt(l['principal'])} | مانده: {fmt(l['remaining_balance'])}", 11),
                    txt(f"{paid} از {len(insts)} قسط کسر شده", 11, color=T()['muted']),
                    txt(f"هدف: {l.get('purpose') or '-'}", 10, color=T()['muted']),
                    ft.Text("\n".join(lines), size=11, selectable=True),
                ], scroll=ft.ScrollMode.AUTO, spacing=6),
                    width=min((self.page.width or 400) - 60, 420),
                    height=min((self.page.height or 600) * 0.6, 480)),
                actions=[tbtn("حذف وام", lambda ev: (self.close_dlg(d), self.confirm(
                    "وام و تمام اقساط حذف شود؟", delete, "حذف وام")), "#c0392b"),
                    tbtn("بستن", lambda ev: self.close_dlg(d))])
            self.open_dlg(d)

        litems = []
        for l in c['loans']:
            e = emps.get(l['emp_id'])
            if not e: continue
            litems.append(card(ft.Row([
                ft.Column([txt(f"{e.get('first_name','')} {e.get('last_name','')}", 12, True),
                           txt(f"اصل: {fmt(l['principal'])} | مانده: {fmt(l['remaining_balance'])} | "
                               f"{l['install_count']} قسط", 10, color=T()['muted'])],
                          spacing=2, expand=True),
                badge("تسویه" if l['status'] == 1 else "جاری",
                      T()['success'] if l['status'] == 1 else T()['accent'],
                      "#ffffff" if l['status'] == 1 else T()['primary'], 9)]),
                padding=8, on_click=lambda ev, ll=l, ee=e: loan_detail(ll, ee)))

        bitems = []
        for b in c['bonuses']:
            if b['year'] != self.year or b['month'] != self.month: continue
            e = emps.get(b['emp_id'])
            if not e: continue
            def make_del(bid):
                return lambda ev: self.confirm("این پاداش حذف شود؟",
                                               lambda: (self.db.delete('bonuses', bid), self.refresh()))
            bitems.append(card(ft.Row([
                ft.Column([txt(f"{e.get('first_name','')} {e.get('last_name','')}", 12, True),
                           txt(f"{fmt(b['amount'])} ریال — {b.get('reason') or ''}", 10,
                               color=T()['muted'])], spacing=2, expand=True),
                iconbtn(_ic("DELETE"), make_del(b['id']), "#c0392b", 18)]), padding=8))

        ditems = []
        for d0 in c.get('deductions', []):
            if d0['year'] != self.year or d0['month'] != self.month: continue
            e = emps.get(d0['emp_id'])
            if not e: continue
            def make_del(did):
                return lambda ev: self.confirm("این کسورات حذف شود؟",
                                               lambda: (self.db.delete('deductions', did), self.refresh()))
            ditems.append(card(ft.Row([
                ft.Column([txt(f"{e.get('first_name','')} {e.get('last_name','')}", 12, True),
                           txt(f"{fmt(d0['amount'])} ریال — {d0.get('reason') or ''}", 10,
                               color=T()['muted'])], spacing=2, expand=True),
                iconbtn(_ic("DELETE"), make_del(d0['id']), "#c0392b", 18)]), padding=8))

        body = [txt("💰 وام‌ها (لمس برای جزئیات/حذف)", 12, True)] + \
               (litems or [self.empty("وامی ثبت نشده")])
        body += [txt(f"🎁 پاداش‌های {MONTHS[self.month-1]} {self.year}", 12, True)] + \
                (bitems or [txt("پاداشی نیست", 10, color=T()['muted'])])
        body += [txt(f"➖ کسورات {MONTHS[self.month-1]} {self.year}", 12, True)] + \
                (ditems or [txt("کسوراتی نیست", 10, color=T()['muted'])])
        return ft.Column([
            ft.Row([
                gbtn("💰 وام", _ic("ADD"), lambda e: loan_form(), T()['success'], expand=True),
                gbtn("🎁 پاداش", _ic("ADD"), lambda e: bonus_form(), T()['primary'], expand=True),
                gbtn("➖ کسورات", _ic("ADD"), lambda e: deduction_form(), T()['danger'], expand=True),
            ], spacing=6),
            self.period_bar(self.refresh),
            ft.ListView(body, expand=True, spacing=6, padding=pad_only(bottom=20))],
            expand=True, spacing=6)

    def v_eid(self):
        c = self.db.company_data(self.cid)
        emps = {e['id']: e for e in c['employees']}
        recs = [r for r in c['eid_records'] if r['year'] == self.year]

        def go(e):
            n = self.svc.calculate_eid(self.cid, self.year)
            self.toast(f"✅ {n} نفر محاسبه شد"); self.refresh()

        def pdf_eid(e):
            if not recs: self.toast("داده‌ای نیست", True); return
            try:
                pdf, _ = _pdf_init((210, 297))
                W, M = 210, 8
                pdf.add_page()
                pdf.set_fill_color(30, 58, 95); pdf.rect(M, 8, W - 2*M, 12, 'F')
                pdf.set_xy(M, 10); pdf.set_font("F", size=13); pdf.set_text_color(240, 180, 41)
                pdf.cell(W - 2*M, 8, rtl(f"گزارش عیدی و سنوات — سال {self.year}"), border=0, align='C')
                y = 26
                headers = ["#", "نام و فامیل", "کارکرد سال", "حقوق ماهانه", "عیدی", "سنوات"]
                col_w = [12, 60, 25, 40, 30, 30]
                pdf.set_fill_color(240, 180, 41); pdf.set_text_color(30, 58, 95); pdf.set_font("F", size=9)
                x = M
                for i, h in enumerate(headers):
                    pdf.set_xy(x, y); pdf.cell(col_w[i], 7, rtl(h), border=1, align='C', fill=True)
                    x += col_w[i]
                y += 7
                pdf.set_text_color(0, 0, 0); pdf.set_font("F", size=8)
                te = ts = 0
                for idx, r in enumerate(recs, 1):
                    emp = emps.get(r['emp_id'])
                    if not emp: continue
                    if y > 275: pdf.add_page(); y = 20
                    vals = [str(idx), f"{emp.get('first_name','')} {emp.get('last_name','')}",
                            f"{r['work_days']:g}", fmt(r.get('monthly_salary') or 0),
                            fmt(r['amount']), fmt(r['severance'])]
                    x = M
                    for i, v in enumerate(vals):
                        pdf.set_xy(x, y); pdf.cell(col_w[i], 6, rtl(v), border=1, align='C')
                        x += col_w[i]
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
            if not e: continue
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
        return ft.ListView([
            self.period_bar(self.refresh), totals, dept_card,
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
                    m = validate(v)
                    if m: return m
                if r: self.db.update(table, r['id'], v)
                else: self.db.insert(table, dict(v, company_id=self.cid))
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


def main(page: ft.Page):
    try:
        App(page, Database()).start()
    except Exception:
        tb = traceback.format_exc(); log_error(tb)
        try:
            page.add(ft.Text("خطای راه‌اندازی:\n" + tb, selectable=True, size=11))
            page.update()
        except Exception: pass

if __name__ == "__main__":
    _safe_ft_run(main)