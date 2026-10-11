# -*- coding: utf-8 -*-
"""
fix_all.py
Fix broken pyproject.toml + workflow + regenerate icon.
Run: python fix_all.py
"""

from pathlib import Path
import sys
import shutil
import datetime

BASE = Path(__file__).parent.resolve()
PYPROJECT = BASE / "pyproject.toml"
WORKFLOW = BASE / ".github" / "workflows" / "build-apk.yml"
ICON = BASE / "assets" / "icon.png"

# --- Clean pyproject.toml (pure ASCII, no encoding issues) ---
PYPROJECT_CLEAN = '''[project]
name = "erfanhesab"
version = "6.1.0"
description = "Comprehensive Payroll Management System"
readme = "README.md"
requires-python = ">=3.10,<3.13"
authors = [{ name = "Erfan Baloch" }]
license = { text = "Proprietary" }
dependencies = [
    "flet==0.28.3",
    "arabic-reshaper>=3.0.0",
    "python-bidi>=0.4.2",
    "fpdf2>=2.7.9",
    "Pillow>=10.4.0",
]

[build-system]
requires = ["setuptools>=68"]
build-backend = "setuptools.build_meta"

[tool.flet]
org = "ir.erfanhesab"
product = "ErfanHesab"
company = "Erfan Baloch"
copyright = "(c) 1405 Erfan Baloch"
build_number = 1
icon = "assets/icon.png"

[tool.flet.app]
path = "."

[tool.flet.android]
package = "ir.erfanhesab.payroll"
min_sdk_version = 21
target_sdk_version = 34

[tool.flet.android.permission]
"android.permission.INTERNET" = true
"android.permission.READ_EXTERNAL_STORAGE" = true
"android.permission.WRITE_EXTERNAL_STORAGE" = true
"android.permission.READ_MEDIA_IMAGES" = true
"android.permission.CAMERA" = true
'''

# --- Clean workflow (valid YAML, no orphan keys) ---
WORKFLOW_CLEAN = '''name: Build Android APK

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

      - name: Accept Android licenses
        run: yes | flutter doctor --android-licenses || true

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
'''


def banner(msg):
    print()
    print("=" * 62)
    print("  " + msg)
    print("=" * 62)


def backup(path):
    if not path.exists():
        return
    stamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    bak = path.with_suffix(path.suffix + f".bak_{stamp}")
    shutil.copy2(path, bak)
    print(f"  [backup] {path.name} -> {bak.name}")


def write_utf8(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(content)
    print(f"  [write ] {path.relative_to(BASE)}  ({len(content)} bytes)")


def fix_pyproject():
    banner("STEP 1/3 - Fix pyproject.toml")
    backup(PYPROJECT)
    write_utf8(PYPROJECT, PYPROJECT_CLEAN)
    print("  OK - pyproject.toml rewritten with clean UTF-8")


def fix_workflow():
    banner("STEP 2/3 - Fix .github/workflows/build-apk.yml")
    backup(WORKFLOW)
    write_utf8(WORKFLOW, WORKFLOW_CLEAN)
    print("  OK - workflow rewritten, YAML is now valid")


def build_icon():
    banner("STEP 3/3 - Regenerate icon.png (1024x1024)")
    try:
        from PIL import Image, ImageDraw, ImageFilter
    except ImportError:
        print("  [!] Pillow not installed. Run: pip install Pillow")
        return False

    size = 1024
    NAVY       = (30, 58, 95, 255)
    NAVY_DARK  = (15, 36, 64, 255)
    NAVY_LIGHT = (45, 90, 140, 255)
    GOLD       = (240, 180, 41, 255)
    GOLD_LIGHT = (255, 220, 130, 255)
    GOLD_DARK  = (200, 145, 20, 255)

    img = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)

    # Background rounded rect
    d.rounded_rectangle([0, 0, size, size], radius=int(size * 0.20), fill=NAVY)

    # Soft glow at top
    glow = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    gd = ImageDraw.Draw(glow)
    gd.ellipse([size * 0.10, -size * 0.15, size * 0.90, size * 0.55],
               fill=(45, 90, 140, 110))
    glow = glow.filter(ImageFilter.GaussianBlur(int(size * 0.05)))
    img.alpha_composite(glow)

    # Gold frame
    inset = int(size * 0.055)
    d.rounded_rectangle([inset, inset, size - inset, size - inset],
                        radius=int(size * 0.155),
                        outline=GOLD,
                        width=int(size * 0.017))

    # Calculator body
    bl, br = int(size * 0.235), int(size * 0.765)
    bt, bb = int(size * 0.245), int(size * 0.815)
    body_r = int(size * 0.075)

    # Shadow
    shadow = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    sd = ImageDraw.Draw(shadow)
    sd.rounded_rectangle([bl + 8, bt + 14, br + 8, bb + 14],
                         radius=body_r, fill=(0, 0, 0, 100))
    shadow = shadow.filter(ImageFilter.GaussianBlur(int(size * 0.015)))
    img.alpha_composite(shadow)

    # Body gold
    d.rounded_rectangle([bl, bt, br, bb], radius=body_r, fill=GOLD)
    d.rounded_rectangle([bl + 10, bt + 8, br - 10, bt + int(size * 0.05)],
                        radius=int(size * 0.04), fill=GOLD_LIGHT)
    d.rounded_rectangle([bl, bb - int(size * 0.02), br, bb],
                        radius=body_r, fill=GOLD_DARK)

    # Screen
    sl = bl + int(size * 0.055)
    sr = br - int(size * 0.055)
    st = bt + int(size * 0.055)
    sb = bt + int(size * 0.185)
    d.rounded_rectangle([sl, st, sr, sb],
                        radius=int(size * 0.022), fill=NAVY_DARK)
    d.rounded_rectangle([sl + int(size * 0.02), st + int(size * 0.02),
                         sr - int(size * 0.02), st + int(size * 0.045)],
                        radius=int(size * 0.012), fill=NAVY_LIGHT)

    # Keypad 3x3
    kl = bl + int(size * 0.05)
    kr = br - int(size * 0.05)
    kt = sb + int(size * 0.035)
    kb = bb - int(size * 0.05)

    cols, rows = 3, 3
    gap = int(size * 0.013)
    bw = (kr - kl - gap * (cols - 1)) / cols
    bh = (kb - kt - gap * (rows - 1)) / rows
    br2 = int(size * 0.016)

    for r in range(rows):
        for cc in range(cols):
            x1 = kl + cc * (bw + gap)
            y1 = kt + r * (bh + gap)
            x2 = x1 + bw
            y2 = y1 + bh

            if r == rows - 1 and cc == cols - 1:
                # Equals button
                d.rounded_rectangle([x1, y1, x2, y2], radius=br2, fill=GOLD_LIGHT)
                cy = (y1 + y2) / 2
                lw = int(size * 0.006)
                d.rounded_rectangle([x1 + bw * 0.28, cy - lw,
                                     x2 - bw * 0.28, cy + lw],
                                    radius=lw, fill=NAVY_DARK)
                d.rounded_rectangle([x1 + bw * 0.28, cy - lw * 4,
                                     x2 - bw * 0.28, cy - lw * 2],
                                    radius=lw, fill=NAVY_DARK)
            else:
                if cc == cols - 1:
                    fill = NAVY_LIGHT
                elif r == 0 and cc == 0:
                    fill = GOLD_DARK
                else:
                    fill = NAVY_DARK
                d.rounded_rectangle([x1, y1, x2, y2], radius=br2, fill=fill)
                d.rounded_rectangle([x1 + bw * 0.18, y1 + bh * 0.18,
                                     x2 - bw * 0.55, y1 + bh * 0.32],
                                    radius=int(bh * 0.06),
                                    fill=(255, 255, 255, 40))

    # Gold coin top-right
    coin_r = int(size * 0.075)
    cx, cy = int(size * 0.79), int(size * 0.235)
    d.ellipse([cx - coin_r, cy - coin_r, cx + coin_r, cy + coin_r],
              fill=GOLD, outline=GOLD_DARK, width=int(size * 0.006))
    d.ellipse([cx - coin_r * 0.65, cy - coin_r * 0.65,
               cx + coin_r * 0.65, cy + coin_r * 0.65],
              outline=GOLD_DARK, width=int(size * 0.004))

    # Save icon
    backup(ICON)
    ICON.parent.mkdir(parents=True, exist_ok=True)
    img.save(ICON, "PNG", optimize=True)

    # Small icons for Android
    for px in (192, 512):
        small = img.resize((px, px), Image.LANCZOS)
        small.save(ICON.parent / f"icon_{px}.png", "PNG", optimize=True)

    size_kb = ICON.stat().st_size / 1024
    print(f"  OK - icon.png regenerated (1024x1024, {size_kb:.1f} KB)")
    print(f"  OK - icon_192.png + icon_512.png also created")
    return True


def main():
    print()
    print("#" * 62)
    print("#  FIX ALL - ErfanHesab project")
    print("#" * 62)

    if not (BASE / "main.py").exists():
        print()
        print("  [X] main.py not found in this folder!")
        print(f"      Current folder: {BASE}")
        sys.exit(1)

    fix_pyproject()
    fix_workflow()
    build_icon()

    banner("DONE - all fixes applied")
    print()
    print("  Next steps - run these in PowerShell:")
    print()
    print("    git add .")
    print("    git commit -m \"fix: clean pyproject + workflow + new icon\"")
    print("    git push origin main")
    print()
    print("  Then open:")
    print("    https://github.com/Tashar790/erfanhesab/actions")
    print()


if __name__ == "__main__":
    main()