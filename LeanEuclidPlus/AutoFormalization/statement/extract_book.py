#!/usr/bin/env python3
"""Extract the English text + diagrams for a book of Euclid's Elements.

Source: the rfitzp open-source LaTeX edition (https://github.com/rfitzp/Elements),
cloned at ELEMENTS_ROOT. Each book is a single .tex file in which every proposition
is a `\\begin{Parallel}` block with `\\ParallelLText{...}` (Greek, ignored) and
`\\ParallelRText{...}` (English, extracted). References such as `[Prop.~1.11]`,
`[Post.~3]`, `[Def.~1.15]`, `[C.N.~3]` are already literal text in the source -- no
`\\ref{}` resolution is needed. Footnotes live *outside* the Parallel block.

This reproduces the deterministic half of how Book 1's data was built. It writes the
FULL English statement+proof+conclusion to `texts_proofs/<n>.txt` and rasterizes the
English figure `figNNe.eps` to `diagrams/<n>.png`. The statement-only `texts/<n>.txt`
(with the `<prf>` marker) and the Lean ground truth are manual per-proposition work --
see Book{N}/WORKFLOW.md.

Usage:
    python extract_book.py --book 2
"""

import argparse
import os
import re
import shutil
import subprocess
import sys

# Root of the cloned rfitzp/Elements LaTeX edition.
ELEMENTS_ROOT = "/u/taddmao/code/autoform/Elements"
# Root of the LeanEuclidPlus benchmark (two levels up from this script's dir).
LEANEUCLID_ROOT = os.path.abspath(
    os.path.join(os.path.dirname(__file__), "..", "..")
)

# Expected proposition counts per book, used as a sanity assertion.
EXPECTED_PROP_COUNT = {2: 14, 3: 37, 4: 16}

# DPI for EPS -> PNG. Book 1's committed PNGs are ~500-540px wide from EPS
# BoundingBoxes ~410pt wide, i.e. roughly 120 DPI.
DIAGRAM_DENSITY = 120


def find_balanced(text, start):
    """Given that text[start] == '{', return the index just past the matching '}'.

    Walks the string tracking brace depth so nested groups like {\\large ...} and
    \\centerline{\\epsffile{...}} are handled correctly.
    """
    assert text[start] == "{", f"expected '{{' at index {start}"
    depth = 0
    i = start
    while i < len(text):
        c = text[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise ValueError("unbalanced braces starting at index %d" % start)


def split_propositions(tex, book):
    """Return [(prop_num, region_text), ...] split on \\pdfbookmark Proposition markers.

    The Definitions block has no such marker and is excluded. Each region runs from
    its marker to the next marker (or EOF), so trailing footnotes after \\end{Parallel}
    are included in the region but ignored later (we only read inside \\ParallelRText).
    """
    marker = re.compile(
        r"\\pdfbookmark\[1\]\{Proposition\s+%d\.(\d+)\}" % book
    )
    matches = list(marker.finditer(tex))
    regions = []
    for idx, m in enumerate(matches):
        num = int(m.group(1))
        start = m.end()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(tex)
        regions.append((num, tex[start:end]))
    return regions


def extract_english(region):
    """Return the brace-balanced body of the first \\ParallelRText{...} in region."""
    m = re.search(r"\\ParallelRText\s*\{", region)
    if not m:
        raise ValueError("no \\ParallelRText block found in proposition region")
    brace_open = m.end() - 1  # index of the '{'
    brace_close = find_balanced(region, brace_open)
    return region[brace_open + 1 : brace_close - 1]


def clean_latex(body):
    """Turn the English \\ParallelRText body into plain text, matching Book 1's style.

    Keeps `$...$` math and `[Ref.~x.y]` citations verbatim; strips figures, the
    Proposition heading, footnote daggers, and layout macros; collapses whitespace.
    """
    # Mask $...$ spans so generic macro stripping never touches math.
    math_spans = []

    def _mask(m):
        math_spans.append(m.group(0))
        return "\x00%d\x00" % (len(math_spans) - 1)

    text = re.sub(r"\$[^$]*\$", _mask, body)

    # Remove the figure: \epsfysize=... and \centerline{\epsffile{...}}.
    text = re.sub(r"\\epsfysize\s*=\s*[^\n]*", "", text)
    text = re.sub(r"\\centerline\s*\{", "{", text)  # unwrap; \epsffile removed next
    text = re.sub(r"\\epsffile\s*\{[^}]*\}", "", text)

    # Remove the centered heading block: \begin{center} ... {\large Proposition N} ... \end{center}.
    text = re.sub(
        r"\\begin\{center\}.*?\\end\{center\}", "", text, flags=re.DOTALL
    )

    # Strip layout / formatting macros (daggers were inside the heading, but also
    # guard against any inline ones).
    text = text.replace("\\\\", " ")  # line breaks
    text = re.sub(r"\\vspace\*?\s*\{[^}]*\}", "", text)
    text = re.sub(r"\\(noindent|large|footnotesize|it|normalsize|huge|Huge)\b", "", text)
    text = re.sub(r"\\ggn\s*\{[^}]*\}", "", text)
    text = re.sub(r"\\gr\s*\{[^}]*\}", "", text)  # any stray Greek (shouldn't occur)

    # Any remaining lone backslash command with no argument we care about.
    text = re.sub(r"\\[a-zA-Z]+\*?", "", text)

    # Drop now-empty braces left behind by unwrapping.
    text = re.sub(r"\{\s*\}", "", text)
    text = text.replace("{", "").replace("}", "")

    # Restore math.
    def _unmask(m):
        return math_spans[int(m.group(1))]

    text = re.sub(r"\x00(\d+)\x00", _unmask, text)

    # Collapse whitespace.
    text = re.sub(r"\s+", " ", text).strip()
    return text


def rasterize(eps_path, png_path):
    """Rasterize an EPS figure to PNG, white background, tight crop, matching Book 1."""
    cmd = [
        "convert",
        "-density",
        str(DIAGRAM_DENSITY),
        eps_path,
        "-background",
        "white",
        "-flatten",
        "-trim",
        "+repage",
        png_path,
    ]
    subprocess.run(cmd, check=True, capture_output=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--book", type=int, required=True, help="Book number, e.g. 2")
    args = ap.parse_args()
    book = args.book

    src_dir = os.path.join(ELEMENTS_ROOT, "Book%02d" % book)
    tex_path = os.path.join(src_dir, "Book%d.tex" % book)
    out_dir = os.path.join(LEANEUCLID_ROOT, "Book%d" % book)
    texts_proofs_dir = os.path.join(out_dir, "texts_proofs")
    diagrams_dir = os.path.join(out_dir, "diagrams")

    if not os.path.isfile(tex_path):
        sys.exit("source tex not found: %s" % tex_path)
    if shutil.which("convert") is None:
        sys.exit("ImageMagick 'convert' not found on PATH (needed for diagrams)")

    os.makedirs(texts_proofs_dir, exist_ok=True)
    os.makedirs(diagrams_dir, exist_ok=True)

    with open(tex_path, encoding="utf-8", errors="replace") as f:
        tex = f.read()

    regions = split_propositions(tex, book)
    print("Found %d propositions in %s" % (len(regions), tex_path))
    expected = EXPECTED_PROP_COUNT.get(book)
    if expected is not None and len(regions) != expected:
        sys.exit(
            "expected %d propositions for Book %d, got %d"
            % (expected, book, len(regions))
        )

    for num, region in regions:
        body = extract_english(region)
        text = clean_latex(body)
        out_txt = os.path.join(texts_proofs_dir, "%d.txt" % num)
        with open(out_txt, "w", encoding="utf-8") as f:
            f.write(text)  # no trailing newline, matching Book 1

        eps = os.path.join(src_dir, "fig%02de.eps" % num)
        out_png = os.path.join(diagrams_dir, "%d.png" % num)
        if os.path.isfile(eps):
            rasterize(eps, out_png)
        else:
            print("  WARNING: missing figure %s (skipping diagram)" % eps)

    print("Wrote %d text files to %s" % (len(regions), texts_proofs_dir))
    print("Wrote diagrams to %s" % diagrams_dir)
    print(
        "\nNext (manual, per proposition): write Book%d/PropNN.lean and the "
        "statement-only Book%d/texts/N.txt with the <prf> marker. See WORKFLOW.md."
        % (book, book)
    )


if __name__ == "__main__":
    main()
