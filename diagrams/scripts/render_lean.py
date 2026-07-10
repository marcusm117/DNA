#!/usr/bin/env python3
"""Render a text/Lean file to a PNG: plain monospace text, transparent background.

No syntax coloring. Only glyph pixels are drawn, so it drops onto any background.

Usage:
    python3 render_lean.py INPUT [OUTPUT.png]
        [--fontsize 30] [--pad 18] [--line-spacing 1.30]
        [--color "#000000"] [--supersample 3] [--font /path/Mono.ttf]

Default output is diagrams/<input-name>.png. Requires: Pillow (pip install pillow).
"""
import argparse
import os
import sys

try:
    from PIL import Image, ImageDraw, ImageFont
except ImportError:
    sys.exit("error: Pillow is required -> pip install pillow")

FONT_CANDIDATES = [
    "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf",
    "/usr/share/fonts/dejavu/DejaVuSansMono.ttf",
    "/usr/share/fonts/TTF/DejaVuSansMono.ttf",
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input")
    ap.add_argument("output", nargs="?", default=None)
    ap.add_argument("--fontsize", type=int, default=30)
    ap.add_argument("--pad", type=int, default=18)
    ap.add_argument("--line-spacing", type=float, default=1.30)
    ap.add_argument("--color", default="#000000")
    ap.add_argument("--supersample", type=int, default=3)
    ap.add_argument("--font", default=None)
    args = ap.parse_args()

    diagrams_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = args.output or os.path.join(
        diagrams_dir, os.path.splitext(os.path.basename(args.input))[0] + ".png"
    )

    font_path = args.font
    if not font_path:
        for p in FONT_CANDIDATES:
            if os.path.exists(p):
                font_path = p
                break
    if not font_path:
        sys.exit("error: no monospace font found; pass --font /path/to/Mono.ttf")

    with open(args.input, encoding="utf-8") as f:
        lines = f.read().rstrip("\n").split("\n")

    ss = max(1, args.supersample)
    font = ImageFont.truetype(font_path, args.fontsize * ss)
    pad = args.pad * ss
    cellw = font.getlength("0")
    ascent, descent = font.getmetrics()
    line_h = int((ascent + descent) * args.line_spacing)

    ncols = max((len(l) for l in lines), default=0)
    W = int(pad * 2 + ncols * cellw)
    H = int(pad * 2 + len(lines) * line_h)

    img = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    draw = ImageDraw.Draw(img)
    for row, line in enumerate(lines):
        y = pad + row * line_h
        for i, ch in enumerate(line):
            draw.text((pad + i * cellw, y), ch, font=font, fill=args.color)

    if ss > 1:
        img = img.resize((W // ss, H // ss), Image.LANCZOS)
    img.save(out)
    print(f"wrote {out}  ({img.width}x{img.height}px)")


if __name__ == "__main__":
    main()
