#!/usr/bin/env python3
"""Rewrite dead flat `import Book.PropNN` → foldered `import Book1.PropNN.Main`.

The flat `Book/` tree is DEAD since the Book1 foldered migration: `Book/` and `Book1/` both
declare `Elements.Book1.proposition_N`, so co-importing them under a wired Main causes
`environment already contains` collisions. Book1/Book2/Book3 must therefore cite the FOLDERED
form `import Book1.PropNN.Main` and NEVER the flat `import Book.PropNN`.

This is the mechanical, idempotent auto-fixer for that rule. It rewrites every
    import Book.PropNN
line (Book1/Book2/Book3 `.lean` files) to
    import Book1.PropNN.Main
and collapses any exact-duplicate `import` lines that result (Lean tolerates dupes; we keep the
tree clean).

VARIANTS: the flat `Book.PropNN` file carried BOTH the plain `proposition_N` AND its primed
variant lemmas (`proposition_N'`, plus flat-only helpers). Those primed lemmas were extracted into
`Book1Variants/PropNN.lean` (module `Book1Variants.PropNN`), which itself re-imports
`Book1.PropNN.Main` — so importing it gives the plain lemma too. `Book1.PropNN.Main` alone does NOT
have the primes. So a prop that has a `Book1Variants/PropNN.lean` file is rewritten to
`import Book1Variants.PropNN` (a superset — safe whether or not the file uses a prime); every other
prop is rewritten to `import Book1.PropNN.Main`. The variant-prop set is read from the filesystem so
it can never drift from what actually exists. Run bare from the repo root:

    python3 scripts/fix_book_imports.py            # apply
    python3 scripts/fix_book_imports.py --dry-run  # show what would change, touch nothing

The conversion is GLOBAL/all-or-nothing by design: converting only some references in a build
tree would leave a flat+foldered mix and re-introduce the very collision we avoid. Verify after
with `scripts/safe_build.sh Book Book1 Book2 Book3` (or `lake build`).
"""
from __future__ import annotations
import re
import sys
from pathlib import Path

# repo layout: scripts/ lives in LeanEuclidPlus/, books are siblings.
LEAN_ROOT = Path(__file__).resolve().parent.parent
BOOK_DIRS = ["Book1", "Book2", "Book3"]

# `import Book.PropNN` (optionally with trailing whitespace) — the flat form. We deliberately do
# NOT match `import Book1.` / `import Book2.` / `import Book.lean`-style aggregators, only the
# `Book.PropNN` proposition modules.
FLAT_RE = re.compile(r'^(?P<indent>[ \t]*)import[ \t]+Book\.(?P<prop>Prop(?P<num>\d+))[ \t]*$')

# Props whose primed variants were extracted to Book1Variants/PropNN.lean — read from disk so the
# set can never drift from reality. `Prop05` (etc.) -> the prop token.
VARIANT_PROPS = {p.stem for p in (LEAN_ROOT / "Book1Variants").glob("Prop*.lean")}


def import_for(prop: str) -> str:
    """The foldered import replacing flat `Book.<prop>`. Variant props go through Book1Variants
    (which re-imports .Main, so the plain proposition is available too); others go straight to .Main."""
    if prop in VARIANT_PROPS:
        return f"import Book1Variants.{prop}"
    return f"import Book1.{prop}.Main"


def convert_text(text: str) -> tuple[str, int]:
    """Return (new_text, n_lines_rewritten). Also drops exact-duplicate import lines."""
    out_lines: list[str] = []
    seen_imports: set[str] = set()
    n_changed = 0
    for line in text.split("\n"):
        m = FLAT_RE.match(line)
        if m:
            line = f"{m.group('indent')}{import_for(m.group('prop'))}"
            n_changed += 1
        # dedup only `import ...` lines (idempotent + collision-clean); leave all else untouched.
        stripped = line.strip()
        if stripped.startswith("import "):
            if stripped in seen_imports:
                # skip this exact-duplicate import line (e.g. flat+foldered collapsed to one)
                if m:
                    n_changed -= 0  # still counts as a rewrite site handled; dup just vanishes
                continue
            seen_imports.add(stripped)
        out_lines.append(line)
    return "\n".join(out_lines), n_changed


def main() -> int:
    dry = "--dry-run" in sys.argv[1:]
    total_files = 0
    total_lines = 0
    for book in BOOK_DIRS:
        base = LEAN_ROOT / book
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            original = path.read_text(encoding="utf-8")
            if "import Book." not in original:
                continue
            new_text, n = convert_text(original)
            if new_text == original:
                continue
            total_files += 1
            total_lines += n
            rel = path.relative_to(LEAN_ROOT)
            print(f"  {rel}  ({n} import{'s' if n != 1 else ''})")
            if not dry:
                path.write_text(new_text, encoding="utf-8")
    verb = "would rewrite" if dry else "rewrote"
    print(f"\n{verb} {total_lines} flat `import Book.PropNN` line(s) across {total_files} file(s).")
    if dry:
        print("(--dry-run: no files touched)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
