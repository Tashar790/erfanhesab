# -*- coding: utf-8 -*-
"""اسکریپت خودکار: اصلاح workflow + push به GitHub + trigger build"""
import os
import subprocess
import sys
from pathlib import Path

BASE = Path(__file__).parent.resolve()
WORKFLOW_FILE = BASE / ".github" / "workflows" / "build-apk.yml"

# ═══════════════════════════════════════════════════════════
# نسخه اصلاح‌شده workflow — بدون خطای Flutter و prompt
# ═══════════════════════════════════════════════════════════
FIXED_WORKFLOW = """name: Build Android APK

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

      - name: 📦 نصب کتابخانه‌های پایتون
        run: |
          python -m pip install --upgrade pip
          pip install flet[all]
          pip install -r requirements.txt

      - name: 📱 ساخت APK
        run: flet build apk --yes --verbose
        env:
          FLET_CLI_YES: '1'
          FLET_CLI_NO_RICH_OUTPUT: '1'

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
"""


def run(cmd, check=True, capture=False):
    """اجرای دستور در shell."""
    print(f"  $ {cmd}")
    result = subprocess.run(
        cmd, shell=True, cwd=str(BASE),
        capture_output=capture, text=True
    )
    if check and result.returncode != 0:
        if capture:
            print(f"  STDERR: {result.stderr}")
        raise RuntimeError(f"دستور ناموفق: {cmd}")
    return result.stdout.strip() if capture else ""


def log_ok(msg): print(f"✅ {msg}")
def log_info(msg): print(f"ℹ️  {msg}")
def log_err(msg): print(f"❌ {msg}")


def main():
    print("\n" + "═" * 60)
    print("  🚀 Deploy خودکار — عرفان حساب")
    print("═" * 60 + "\n")

    # ۱. اصلاح workflow
    print("📝 گام ۱: اصلاح فایل workflow")
    WORKFLOW_FILE.parent.mkdir(parents=True, exist_ok=True)
    WORKFLOW_FILE.write_text(FIXED_WORKFLOW, encoding='utf-8')
    log_ok(f"workflow اصلاح شد → {WORKFLOW_FILE.relative_to(BASE)}")

    # ۲. Commit و Push
    print("\n📤 گام ۲: push به GitHub")
    try:
        run("git add .", capture=True)
        result = run('git commit -m "fix: workflow with --yes and FLET_CLI_YES"',
                     check=False, capture=True)
        if "nothing to commit" in (result or ""):
            log_info("تغییری برای commit نیست، از commit خالی استفاده می‌کنم")
            run('git commit --allow-empty -m "trigger: rebuild APK"', capture=True)
        else:
            log_ok("commit انجام شد")
    except Exception as e:
        log_err(f"خطا در commit: {e}")
        return 1

    try:
        run("git push origin main", capture=True)
        log_ok("push به GitHub انجام شد")
    except Exception as e:
        log_err(f"خطا در push: {e}")
        log_info("اگه خطای authentication دادی، با توکن GitHub دوباره امتحان کن")
        return 1

    # ۳. راهنمای بعدی
    print("\n" + "═" * 60)
    print("  🎉 آماده شد! مراحل بعدی:")
    print("═" * 60)
    print("""
  ۱. برو به: https://github.com/Tashar790/erfanhesab/actions
  ۲. workflow سبز/زرد رو می‌بینی (خودکار شروع شد)
  ۳. صبر کن ۱۰-۱۵ دقیقه
  ۴. تیک سبز ✅ که اومد، روی workflow کلیک کن
  ۵. پایین صفحه → بخش Artifacts → دانلود erfanhesab-apk
  ۶. فایل zip رو باز کن → APK آماده است!
""")
    return 0


if __name__ == "__main__":
    sys.exit(main())