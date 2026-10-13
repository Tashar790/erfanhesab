# -*- coding: utf-8 -*-
"""fix_workflow_v2.py — حذف setup-android مشکل‌دار"""

from pathlib import Path

BASE = Path(__file__).parent.resolve()
WORKFLOW = BASE / ".github" / "workflows" / "build-apk.yml"

# ورک‌فلوی ساده و پایدار — بدون setup-android
NEW_WORKFLOW = """name: Build Android APK

on:
  push:
    branches: [ main, master ]
  workflow_dispatch:

jobs:
  build-apk:
    runs-on: ubuntu-latest
    timeout-minutes: 60

    steps:
      - name: Checkout code
        uses: actions/checkout@v4

      - name: Setup Python 3.12
        uses: actions/setup-python@v5
        with:
          python-version: '3.12'
          cache: 'pip'

      - name: Setup Java JDK 17
        uses: actions/setup-java@v4
        with:
          distribution: 'temurin'
          java-version: '17'

      - name: Setup Flutter
        uses: subosito/flutter-action@v2
        with:
          flutter-version: '3.29.2'
          channel: 'stable'
          cache: true

      - name: Install system libraries
        run: |
          sudo apt-get update
          sudo apt-get install -y libgtk-3-dev ninja-build pkg-config

      - name: Install Python dependencies
        run: |
          python -m pip install --upgrade pip
          pip install -r requirements.txt

      - name: Build APK
        run: flet build apk --verbose
        env:
          FLET_CLI_YES: '1'
          CI: 'true'

      - name: Upload APK artifact
        if: success()
        uses: actions/upload-artifact@v4
        with:
          name: erfanhesab-apk
          path: build/apk/*.apk
          if-no-files-found: error
          retention-days: 30
"""

def main():
    WORKFLOW.parent.mkdir(parents=True, exist_ok=True)
    WORKFLOW.write_text(NEW_WORKFLOW, encoding='utf-8')
    print(f"[OK] workflow updated: {WORKFLOW}")
    print()
    print("Next commands:")
    print("  git add .")
    print("  git commit -m \"fix: remove buggy setup-android step\"")
    print("  git push origin main")

if __name__ == "__main__":
    main()