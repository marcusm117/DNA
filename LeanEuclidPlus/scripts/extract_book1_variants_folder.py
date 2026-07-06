#!/usr/bin/env python3
"""Move the per-prop Book1/PropNN/variants.lean into a shared Book1Variants/ tree.

Before: module Book1.PropNN.variants   (file Book1/PropNN/variants.lean)
After:  module Book1Variants.PropNN     (file Book1Variants/PropNN.lean)

The whole change is one module rename applied everywhere:
    Book1.PropM.variants  ->  Book1Variants.PropM
plus physically relocating the files and writing a Book1Variants.lean root so
`lake build Book1Variants` prebuilds them all (for the future benchmark).

Namespaces are unchanged (the theorems stay `Elements.Book1.proposition_N'`); only the
MODULE path moves. `import Book1.PropN.Main` lines inside the variants are left as-is
(the plain proposition_N still comes from the faithful Main for now — revisit when the
BookOriginal baseline tree exists).

Run from LeanEuclidPlus/:   python3 scripts/extract_book1_variants_folder.py
Then:                       lake build Book1Variants && lake build Book1
Reversible with git.
"""
import re, pathlib

ROOT  = pathlib.Path(__file__).resolve().parent.parent   # LeanEuclidPlus/
BOOK1 = ROOT / "Book1"
B1V   = ROOT / "Book1Variants"

VARIANT_PROPS = {1, 2, 5, 9, 11, 22, 23, 29, 34, 35, 36, 37, 42, 44, 46}
RENAME = re.compile(r'\bBook1\.Prop(\d+)\.variants\b')   # -> Book1Variants.Prop\1

def rename(text: str) -> str:
    return RENAME.sub(r'Book1Variants.Prop\1', text)

def main() -> None:
    B1V.mkdir(exist_ok=True)

    # 1. relocate each variants file, rewriting its own module references
    moved = 0
    for n in sorted(VARIANT_PROPS):
        src = BOOK1 / f"Prop{n:02d}" / "variants.lean"
        if not src.exists():
            raise SystemExit(f"missing {src} (run migrate_book1_variants.py first)")
        (B1V / f"Prop{n:02d}.lean").write_text(rename(src.read_text()))
        src.unlink()
        moved += 1
    print(f"  moved {moved} variants file(s) into Book1Variants/")

    # 2. repoint every remaining reference across Book1/ and Book1Variants/
    touched = 0
    for p in sorted(list(BOOK1.rglob("*.lean")) + list(B1V.rglob("*.lean"))):
        t = p.read_text()
        nt = rename(t)
        if nt != t:
            p.write_text(nt)
            touched += 1
    print(f"  repointed references in {touched} file(s)")

    # 3. write the Book1Variants.lean root (aggregator) for `lake build Book1Variants`
    roots = "\n".join(f"import Book1Variants.Prop{n:02d}" for n in sorted(VARIANT_PROPS))
    (ROOT / "Book1Variants.lean").write_text(roots + "\n")
    print("  wrote Book1Variants.lean root")

    # 4. sanity: no stale Book1.PropM.variants reference should remain
    leaks = [str(p.relative_to(ROOT)) for p in list(BOOK1.rglob("*.lean")) + list(B1V.rglob("*.lean"))
             if RENAME.search(p.read_text())]
    if leaks:
        raise SystemExit("LEAK: stale .variants module refs remain:\n  " + "\n  ".join(leaks))
    print("Done. Now: lake build Book1Variants && lake build Book1")

if __name__ == "__main__":
    main()
