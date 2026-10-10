# -*- coding: utf-8 -*-
"""
اسکریپت خودکار ساختار پروژه عرفان حساب
طراحی‌شده برای آماده‌سازی push به GitHub و ساخت APK
"""
import os
import sys
import urllib.request
import urllib.error
import zipfile
import io
import struct
import zlib
from pathlib import Path

# ═══════════════════════════════════════════════════════════
# مسیر پایه: پوشه‌ای که این اسکریپت در آن قرار دارد
# ═══════════════════════════════════════════════════════════
BASE = Path(__file__).parent.resolve()

# ═══════════════════════════════════════════════════════════
# رنگ‌ها برای چاپ زیبا در ترمینال
# ═══════════════════════════════════════════════════════════
class C:
    RESET = "\033[0m"
    RED = "\033[91m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    BLUE = "\033[94m"
    MAGENTA = "\033[95m"
    CYAN = "\033[96m"
    BOLD = "\033[1m"

def log_ok(msg): print(f"{C.GREEN}✅ {msg}{C.RESET}")
def log_info(msg): print(f"{C.CYAN}ℹ️  {msg}{C.RESET}")
def log_warn(msg): print(f"{C.YELLOW}⚠️  {msg}{C.RESET}")
def log_err(msg): print(f"{C.RED}❌ {msg}{C.RESET}")
def log_title(msg): print(f"\n{C.BOLD}{C.MAGENTA}{'═' * 60}{C.RESET}\n{C.BOLD}{C.MAGENTA}  {msg}{C.RESET}\n{C.BOLD}{C.MAGENTA}{'═' * 60}{C.RESET}")


# ═══════════════════════════════════════════════════════════
# ۱. محتوای فایل‌ها
# ═══════════════════════════════════════════════════════════

PYPROJECT_TOML = '''[project]
name = "erfanhesab"
version = "6.1.0"
description = "سیستم جامع حقوق و دستمزد عرفان حساب"
requires-python = ">=3.9"
authors = [
    { name = "عرفان بلوچ" }
]
dependencies = [
    "flet[all]>=0.28.0",
    "arabic-reshaper>=3.0.0",
    "python-bidi>=0.4.2",
    "fpdf2>=2.7.9",
    "Pillow>=10.0.0",
]

[tool.flet]
org = "ir.erfanhesab"
product = "عرفان حساب"
company = "عرفان بلوچ"
copyright = "© 1405 عرفان بلوچ"

[tool.flet.app]
path = "."

[tool.flet.android]
package = "ir.erfanhesab.payroll"

[tool.flet.android.permission]
"android.permission.INTERNET" = true
"android.permission.READ_EXTERNAL_STORAGE" = true
"android.permission.WRITE_EXTERNAL_STORAGE" = true
'''

REQUIREMENTS_TXT = '''flet[all]>=0.28.0
arabic-reshaper>=3.0.0
python-bidi>=0.4.2
fpdf2>=2.7.9
Pillow>=10.0.0
'''

BUILD_WORKFLOW_YML = '''name: Build Android APK

on:
  push:
    branches: [ main, master ]
  workflow_dispatch:

jobs:
  build-apk:
    runs-on: ubuntu-latest

    steps:
      - name: 📥 دریافت کد
        uses: actions/checkout@v4

      - name: 🐍 نصب Python 3.12
        uses: actions/setup-python@v5
        with:
          python-version: '3.12'

      - name: ☕ نصب Java JDK 17
        uses: actions/setup-java@v4
        with:
          distribution: 'temurin'
          java-version: '17'

      - name: 🎯 نصب Android SDK
        uses: android-actions/setup-android@v3
        with:
          packages: 'platforms;android-34 build-tools;34.0.0'
          accept-android-sdk-licenses: true

      - name: 🦋 نصب Flutter
        uses: subosito/flutter-action@v2
        with:
          flutter-version: '3.29.2'
          channel: 'stable'
          cache: true

      - name: 📦 نصب کتابخانه‌های پایتون
        run: |
          python -m pip install --upgrade pip
          pip install flet[all]
          pip install -r requirements.txt

      - name: 📱 ساخت APK
        run: flet build apk --verbose

      - name: 📤 آپلود APK
        if: success()
        uses: actions/upload-artifact@v4
        with:
          name: erfanhesab-apk
          path: build/apk/*.apk
          retention-days: 30

      - name: 🚀 انتشار در Release (فقط با tag)
        if: startsWith(github.ref, 'refs/tags/')
        uses: softprops/action-gh-release@v1
        with:
          files: build/apk/*.apk
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
'''

GITIGNORE = '''# Python
__pycache__/
*.py[cod]
*.egg-info/
.venv/
venv/
env/
.pytest_cache/

# Flet
build/
build_*/

# OS
.DS_Store
Thumbs.db

# IDE
.vscode/
.idea/
*.swp

# Database
*.db
*.db-journal
*.sqlite
*.sqlite3

# Logs
*.log

# Backups
*.before_restore
'''

README_MD = '''# عرفان حساب 6.1

سیستم جامع حقوق و دستمزد — ساخته‌شده با Flet

## ✨ امکانات

- 👤 مدیریت پرسنل با ۳۲ فیلد + عکس پروفایل
- ⏱️ تایم‌شیت دقیق (روز + ساعت + دقیقه)
- 🧮 محاسبه خودکار حقوق، بیمه، مالیات
- 🎁 عیدی و سنوات طبق قانون کار ۱۴۰۵
- 📄 قرارداد کار قابل ویرایش با متغیر پویا
- 🚫 استثنا مزایا بر اساس پرسنل/دپارتمان
- 💰 مدیریت وام، پاداش، کسورات
- 📊 خروجی PDF و CSV
- 💾 پشتیبان‌گیری خودکار SQLite
- 🔐 رمزنگاری PBKDF2

## 📱 ساخت APK

از طریق GitHub Actions خودکار ساخته می‌شود.

### مراحل:
1. کد را به GitHub push کنید
2. به تب **Actions** بروید
3. روی **Build Android APK** کلیک کنید
4. پس از ۱۰-۱۵ دقیقه، APK را از **Artifacts** دانلود کنید

## 🛠️ توسعه‌دهنده

**عرفان بلوچ** | 09029912252

## 📜 مجوز

© 1405 عرفان بلوچ — تمام حقوق محفوظ است
'''


# ═══════════════════════════════════════════════════════════
# ۲. تولید آیکون PNG ساده بدون نیاز به Pillow
# ═══════════════════════════════════════════════════════════
def create_simple_png_icon(path, size=512):
    """ساخت یک PNG آیکون ساده با طرح ماشین حساب."""
    try:
        from PIL import Image, ImageDraw
        # اگر Pillow هست، آیکون زیباتر بساز
        img = Image.new('RGB', (size, size), '#1e3a5f')
        draw = ImageDraw.Draw(img)

        # پس‌زمینه داخلی
        margin = size // 8
        draw.rounded_rectangle(
            [margin, margin, size - margin, size - margin],
            radius=size // 12, fill='#f0b429')

        # صفحه نمایش
        inner_margin = margin + size // 16
        screen_h = size // 5
        draw.rounded_rectangle(
            [inner_margin, inner_margin,
             size - inner_margin, inner_margin + screen_h],
            radius=size // 40, fill='#1e3a5f')

        # دکمه‌ها
        btn_size = size // 8
        gap = size // 40
        start_x = inner_margin + gap
        start_y = inner_margin + screen_h + gap * 3

        for row in range(3):
            for col in range(3):
                x = start_x + col * (btn_size + gap)
                y = start_y + row * (btn_size + gap)
                if x + btn_size < size - inner_margin and y + btn_size < size - inner_margin:
                    draw.rounded_rectangle(
                        [x, y, x + btn_size, y + btn_size],
                        radius=size // 60, fill='#1e3a5f')

        img.save(path, 'PNG')
        return True
    except ImportError:
        # Pillow نیست → PNG خام بساز
        return create_raw_png(path, size)


def create_raw_png(path, size=512):
    """ساخت PNG بدون Pillow با استفاده از zlib."""
    # رنگ پس‌زمینه: نیلی سلطنتی (#1e3a5f)
    bg_color = (0x1e, 0x3a, 0x5f)
    # رنگ طلایی (#f0b429)
    accent = (0xf0, 0xb4, 0x29)
    white = (0xff, 0xff, 0xff)

    # ساخت پیکسل‌ها
    pixels = []
    center = size // 2
    # رسم دایره طلایی در وسط
    for y in range(size):
        row = [b'\x00']  # filter byte
        for x in range(size):
            # فاصله از مرکز
            dx = x - center
            dy = y - center
            dist = (dx * dx + dy * dy) ** 0.5
            if dist < size * 0.42:
                r, g, b = accent
            else:
                r, g, b = bg_color
            # دایره سفید کوچک داخل (به عنوان نماد)
            if dist < size * 0.15:
                r, g, b = white
            # علامت + روی سفیدی
            if dist < size * 0.12 and (abs(dx) < size * 0.015 or abs(dy) < size * 0.015):
                r, g, b = bg_color
            row.append(bytes([r, g, b]))
        pixels.append(b''.join(row))

    raw_data = b''.join(pixels)

    # ساخت chunk های PNG
    def make_chunk(chunk_type, data):
        chunk = chunk_type + data
        crc = zlib.crc32(chunk) & 0xffffffff
        return struct.pack('>I', len(data)) + chunk + struct.pack('>I', crc)

    # IHDR
    ihdr = struct.pack('>IIBBBBB', size, size, 8, 2, 0, 0, 0)

    # IDAT
    compressed = zlib.compress(raw_data, 9)

    png_data = b'\x89PNG\r\n\x1a\n'
    png_data += make_chunk(b'IHDR', ihdr)
    png_data += make_chunk(b'IDAT', compressed)
    png_data += make_chunk(b'IEND', b'')

    with open(path, 'wb') as f:
        f.write(png_data)
    return True


# ═══════════════════════════════════════════════════════════
# ۳. دانلود فونت وزیرمتن
# ═══════════════════════════════════════════════════════════
FONT_URLS = [
    # منابع مختلف برای دانلود فونت
    "https://github.com/rastikerdar/vazirmatn/raw/master/fonts/ttf/Vazirmatn-Regular.ttf",
    "https://raw.githubusercontent.com/rastikerdar/vazirmatn/master/fonts/ttf/Vazirmatn-Regular.ttf",
    "https://cdn.jsdelivr.net/gh/rastikerdar/vazirmatn@master/fonts/ttf/Vazirmatn-Regular.ttf",
]


def download_font(dest_path):
    """دانلود فونت وزیرمتن از منابع مختلف."""
    for url in FONT_URLS:
        try:
            log_info(f"تلاش برای دانلود از: {url}")
            req = urllib.request.Request(
                url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=30) as r:
                data = r.read()
                if len(data) < 10000:
                    log_warn(f"فایل کوچک است ({len(data)} بایت)، رد می‌شوم")
                    continue
                with open(dest_path, 'wb') as f:
                    f.write(data)
                log_ok(f"فونت دانلود شد ({len(data):,} بایت)")
                return True
        except Exception as ex:
            log_warn(f"ناموفق: {ex}")
            continue
    return False


# ═══════════════════════════════════════════════════════════
# ۴. ساخت ساختار پروژه
# ═══════════════════════════════════════════════════════════
def ensure_dir(path):
    """اطمینان از وجود پوشه."""
    Path(path).mkdir(parents=True, exist_ok=True)
    return path


def write_file(path, content, description=""):
    """نوشتن فایل با محتوا."""
    try:
        path = Path(path)
        ensure_dir(path.parent)
        path.write_text(content, encoding='utf-8')
        log_ok(f"{description or path.name} ساخته شد → {path.relative_to(BASE)}")
        return True
    except Exception as ex:
        log_err(f"خطا در ساخت {path}: {ex}")
        return False


def check_main_exists():
    """بررسی وجود main.py."""
    main_path = BASE / "main.py"
    if not main_path.exists():
        log_err(f"فایل main.py در {BASE} پیدا نشد!")
        log_info("لطفاً این اسکریپت را در همان پوشه‌ای که main.py قرار دارد اجرا کنید.")
        return False
    size = main_path.stat().st_size
    log_ok(f"main.py پیدا شد ({size:,} بایت)")
    return True


def build_structure():
    """ساخت کل ساختار پروژه."""
    print(f"\n{C.BOLD}{C.BLUE}🚀 شروع ساخت ساختار پروژه در: {BASE}{C.RESET}\n")

    # ── بررسی main.py ──
    log_title("گام ۱: بررسی فایل اصلی")
    if not check_main_exists():
        return False

    # ── ساخت پوشه‌ها ──
    log_title("گام ۲: ساخت پوشه‌ها")
    dirs = [
        BASE / ".github" / "workflows",
        BASE / "assets",
        BASE / "assets" / "fonts",
    ]
    for d in dirs:
        ensure_dir(d)
        log_ok(f"پوشه: {d.relative_to(BASE)}")

    # ── فایل‌های متنی ──
    log_title("گام ۳: ساخت فایل‌های پیکربندی")
    write_file(BASE / "pyproject.toml", PYPROJECT_TOML, "pyproject.toml")
    write_file(BASE / "requirements.txt", REQUIREMENTS_TXT, "requirements.txt")
    write_file(BASE / ".gitignore", GITIGNORE, ".gitignore")
    write_file(BASE / "README.md", README_MD, "README.md")
    write_file(BASE / ".github" / "workflows" / "build-apk.yml",
               BUILD_WORKFLOW_YML, "build-apk.yml")

    # ── آیکون ──
    log_title("گام ۴: ساخت آیکون برنامه")
    icon_path = BASE / "assets" / "icon.png"
    if icon_path.exists():
        log_info(f"آیکون از قبل وجود دارد → {icon_path.relative_to(BASE)}")
    else:
        try:
            create_simple_png_icon(str(icon_path), size=512)
            log_ok(f"آیکون ساخته شد → assets/icon.png")
        except Exception as ex:
            log_err(f"خطا در ساخت آیکون: {ex}")

    # ── فونت ──
    log_title("گام ۵: دانلود فونت فارسی")
    font_path = BASE / "assets" / "fonts" / "Vazirmatn-Regular.ttf"
    if font_path.exists() and font_path.stat().st_size > 10000:
        log_info(f"فونت از قبل وجود دارد ({font_path.stat().st_size:,} بایت)")
    else:
        if not download_font(str(font_path)):
            log_err("دانلود فونت ناموفق بود!")
            log_info("لطفاً فونت را دستی از این آدرس دانلود کنید:")
            log_info("https://github.com/rastikerdar/vazirmatn/raw/master/fonts/ttf/Vazirmatn-Regular.ttf")
            log_info(f"و در پوشه {font_path.parent} با نام Vazirmatn-Regular.ttf بگذارید.")

    # ── گزارش نهایی ──
    log_title("🎉 ساختار پروژه آماده شد!")
    print(f"\n{C.BOLD}ساختار نهایی:{C.RESET}")
    print_tree(BASE, prefix="")
    print(f"\n{C.BOLD}{C.GREEN}مراحل بعدی:{C.RESET}")
    print(f"  {C.YELLOW}۱.{C.RESET} یک ریپازیتوری در GitHub بسازید")
    print(f"  {C.YELLOW}۲.{C.RESET} در همین پوشه این دستورات را بزنید:")
    print(f"      {C.CYAN}git init{C.RESET}")
    print(f"      {C.CYAN}git add .{C.RESET}")
    print(f"      {C.CYAN}git commit -m \"نسخه اولیه\"{C.RESET}")
    print(f"      {C.CYAN}git branch -M main{C.RESET}")
    print(f"      {C.CYAN}git remote add origin https://github.com/USERNAME/erfanhesab.git{C.RESET}")
    print(f"      {C.CYAN}git push -u origin main{C.RESET}")
    print(f"\n  {C.YELLOW}۳.{C.RESET} در GitHub به تب {C.BOLD}Actions{C.RESET} بروید")
    print(f"  {C.YELLOW}۴.{C.RESET} روی {C.BOLD}Build Android APK{C.RESET} کلیک کنید")
    print(f"  {C.YELLOW}۵.{C.RESET} پس از ۱۰-۱۵ دقیقه، APK را از Artifacts دانلود کنید\n")
    return True


def print_tree(root, prefix="", is_last=True):
    """چاپ درخت پوشه‌ها."""
    root = Path(root)
    # فایل‌های مهم را نشان بده
    items = sorted([p for p in root.iterdir()
                    if not p.name.startswith('.') or p.name == '.github'],
                   key=lambda p: (not p.is_dir(), p.name))

    for i, item in enumerate(items):
        last = (i == len(items) - 1)
        connector = "└── " if last else "├── "
        color = C.CYAN if item.is_dir() else C.GREEN
        print(f"{prefix}{connector}{color}{item.name}{C.RESET}")

        if item.is_dir() and item.name not in ('__pycache__', 'build', '.git'):
            new_prefix = prefix + ("    " if last else "│   ")
            print_tree(item, new_prefix, last)


# ═══════════════════════════════════════════════════════════
# ۵. اجرا
# ═══════════════════════════════════════════════════════════
def main():
    print(f"""{C.BOLD}{C.MAGENTA}
╔══════════════════════════════════════════════════════════╗
║                                                          ║
║        🚀 راه‌انداز خودکار پروژه عرفان حساب 6.1         ║
║                                                          ║
║        این اسکریپت کل ساختار پروژه را برای              ║
║        ساخت APK با GitHub Actions آماده می‌کند          ║
║                                                          ║
╚══════════════════════════════════════════════════════════╝
{C.RESET}""")

    try:
        success = build_structure()
        if success:
            print(f"{C.BOLD}{C.GREEN}✅ تمام!" +
                  f" پروژه شما آماده push به GitHub است.{C.RESET}\n")
            sys.exit(0)
        else:
            print(f"\n{C.RED}❌ ساخت با مشکل مواجه شد.{C.RESET}\n")
            sys.exit(1)
    except KeyboardInterrupt:
        print(f"\n{C.YELLOW}لغو شد.{C.RESET}\n")
        sys.exit(130)
    except Exception as ex:
        log_err(f"خطای غیرمنتظره: {ex}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()