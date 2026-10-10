# -*- coding: utf-8 -*-
"""اسکریپت اصلاح فایل workflow گیت‌هاب"""
from pathlib import Path

BASE = Path(__file__).parent.resolve()
WORKFLOW = BASE / ".github" / "workflows" / "build-apk.yml"

NEW_WORKFLOW = """name: Build Android APK

on:
  push:
    branches: [ main, master ]
  workflow_dispatch:

jobs:
  build-apk:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: actions/setup-python@v5
        with:
          python-version: '3.12'

      - uses: subosito/flutter-action@v2
        with:
          channel: stable

      - name: Install packages
        run: |
          pip install flet[all]
          pip install -r requirements.txt

      - name: Build APK
        run: yes | flet build apk --verbose
        env:
          FLET_CLI_YES: '1'

      - uses: actions/upload-artifact@v4
        with:
          name: erfanhesab-apk
          path: build/apk/*.apk
"""

def main():
    print("📁 مسیر:", WORKFLOW)
    WORKFLOW.parent.mkdir(parents=True, exist_ok=True)
    WORKFLOW.write_text(NEW_WORKFLOW, encoding="utf-8")
    print("✅ فایل workflow با موفقیت نوشته شد!")
    print(f"📏 حجم: {WORKFLOW.stat().st_size} بایت")
    print("\n📤 حالا این دستور رو بزن:")
    print("   git add . ; git commit -m 'fix workflow' ; git push origin main")

if __name__ == "__main__":
    main()