#!/usr/bin/env python3
"""Book1-vs-Book signature parity — sanity-check that every faithful `Book1/PropNN/Main.lean`
restates its canonical `Book/PropNN.lean` proposition with a BYTE-identical statement (up to
whitespace: newlines and spaces are normalized away, nothing else).

The faithful pipeline re-proves the BODY of each proposition, but the STATEMENT
(`theorem proposition_N : <type> :=`) must stay identical to the trusted `Book/` original. This
script pairs the two by proposition name and diffs the whitespace-normalized `<type>`.

  python3 scripts/check_book_parity.py

Pairs by proposition name (primes preserved: `proposition_1` vs `proposition_1'` are distinct):
  - MISMATCH        : name defined in BOTH, but the signatures differ  -> FAIL
  - MISSING-IN-BOOK : name in a Book1 Main with no Book counterpart     -> FAIL
  - book-only       : name only in Book/ (the primed helper variants,   -> INFO (expected)
                      or a prop not yet mirrored into Book1) — not a failure

Reuses `check_signatures.py`'s parser (DECL regex, strip_comments, norm) so the extraction rules
stay identical to the signature-baseline guard. Exits 1 on any MISMATCH or MISSING-IN-BOOK.
"""
import sys, os, glob

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_signatures import DECL, strip_comments, norm, BOOK_ROOT


def _sigs(pattern):
    """{name -> {file, line, sig}} for every proposition signature under a glob pattern
    (relative to BOOK_ROOT). Keyed by bare proposition name so Book/ and Book1/ pair up."""
    out = {}
    for path in sorted(glob.glob(os.path.join(BOOK_ROOT, pattern))):
        rel = os.path.relpath(path, BOOK_ROOT)
        src = strip_comments(open(path, encoding="utf-8").read())
        for m in DECL.finditer(src):
            name = m.group(1)
            line = src.count("\n", 0, m.start()) + 1
            if name in out:
                print(f"WARNING: duplicate {name} ({out[name]['file']}:{out[name]['line']} "
                      f"and {rel}:{line})")
            out[name] = {"file": rel, "line": line, "sig": norm(m.group(2))}
    return out


def main():
    book  = _sigs("Book/Prop*.lean")
    book1 = _sigs("Book1/Prop*/Main.lean")

    mismatch, missing, ok = [], [], []
    for name in sorted(book1):
        if name not in book:
            missing.append(name)
        elif book[name]["sig"] != book1[name]["sig"]:
            mismatch.append(name)
        else:
            ok.append(name)

    for name in mismatch:
        b, b1 = book[name], book1[name]
        print(f"MISMATCH  {name}")
        print(f"    Book  {b['file']}:{b['line']}: {b['sig']}")
        print(f"    Book1 {b1['file']}:{b1['line']}: {b1['sig']}")
    for name in missing:
        b1 = book1[name]
        print(f"MISSING-IN-BOOK  {name}  ({b1['file']}:{b1['line']} has no Book/ counterpart)")

    book_only = sorted(set(book) - set(book1))
    if book_only:
        print(f"\nbook-only (not mirrored in Book1 — primed variants / not-yet-faithful, OK): "
              f"{', '.join(book_only)}")

    if mismatch or missing:
        print(f"\nFAIL: {len(mismatch)} mismatched, {len(missing)} missing-in-Book "
              f"({len(ok)} OK)")
        return 1
    print(f"\nOK: all {len(ok)} Book1 proposition signatures match Book/ (up to whitespace)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
