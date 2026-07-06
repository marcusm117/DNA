#!/usr/bin/env python3
"""Option B: decouple Book1 from flat Book/ so the `Book1` aggregate builds.

The foldered Book1/PropNN/Main.lean files cite earlier props by importing the FLAT
Book/PropM.lean, which declares the SAME name `Elements.Book1.proposition_M` as the
foldered Book1/PropM/Main.lean. Individually fine; in the `Book1` aggregate both copies
land in one environment -> "environment already contains ...". This script removes flat
`Book/` from Book1's import graph entirely:

  1. For each flat Book/PropN.lean that defines primed variants (proposition_N', ...),
     write Book1/PropN/variants.lean containing EVERY theorem EXCEPT the plain
     `proposition_N` (i.e. the primed variants, plus any helper lemmas that live only in
     the flat file, e.g. Prop44's helper_44_between_*). Namespace stays Elements.Book1;
     the plain proposition_N is pulled from Book1.PropN.Main. Imports are repointed (below).

  2. Repoint every `import Book.PropM` under Book1/ to the Book1 equivalent:
        M has variants  -> import Book1.PropM.variants   (which re-imports .Main, so the
                                                           plain proposition_M is available too)
        M has none      -> import Book1.PropM.Main

Flat Book/ is never modified (Book2/Book3/Helpers still use it). Reversible with git.
Idempotent: variants files are regenerated; already-repointed imports are left alone.

Run from LeanEuclidPlus/:   python3 scripts/migrate_book1_variants.py
Then:                       lake build Book1
"""
import re, sys, pathlib

ROOT  = pathlib.Path(__file__).resolve().parent.parent   # LeanEuclidPlus/
BOOK  = ROOT / "Book"
BOOK1 = ROOT / "Book1"

# props whose flat file carries primed variants (verified against Book/Prop*.lean)
VARIANT_PROPS = {1, 2, 5, 9, 11, 22, 23, 29, 34, 35, 36, 37, 42, 44, 46}

IMPORT_RE = re.compile(r'^import Book\.Prop(\d+)\s*$')
THM_RE    = re.compile(r'^theorem\s+(\S+?)\s*(?::|$)')

def repoint_import(m: int) -> str:
    sub = "variants" if m in VARIANT_PROPS else "Main"
    return f"import Book1.Prop{m:02d}.{sub}"

def gen_variants(n: int) -> None:
    src = (BOOK / f"Prop{n:02d}.lean").read_text().splitlines()
    try:
        end_i = next(i for i, l in enumerate(src) if l.strip() == "end Elements.Book1")
    except StopIteration:
        sys.exit(f"Prop{n:02d}: no 'end Elements.Book1' line")
    thms = []
    for i, l in enumerate(src):
        mm = THM_RE.match(l)
        if mm:
            thms.append((i, mm.group(1)))
    if not thms:
        sys.exit(f"Prop{n:02d}: no theorems found")
    plain = f"proposition_{n}"
    if not any(name == plain for _, name in thms):
        sys.exit(f"Prop{n:02d}: plain '{plain}' not found (unexpected shape)")

    # repoint the top-of-file imports
    out_imports = []
    for l in src:
        if not l.startswith("import "):
            continue
        mm = IMPORT_RE.match(l)
        out_imports.append(repoint_import(int(mm.group(1))) if mm else l)
    main_imp = f"import Book1.Prop{n:02d}.Main"
    if main_imp not in out_imports:
        out_imports.append(main_imp)

    # emit every theorem block except the plain proposition_N
    body, kept = [], 0
    for k, (ti, name) in enumerate(thms):
        stop = thms[k + 1][0] if k + 1 < len(thms) else end_i
        if name == plain:
            continue
        body.extend(src[ti:stop])
        kept += 1
    while body and body[-1].strip() == "":
        body.pop()

    content = "\n".join(out_imports + ["", "namespace Elements.Book1", ""]
                        + body + ["", "end Elements.Book1", ""])
    dest = BOOK1 / f"Prop{n:02d}" / "variants.lean"
    if not dest.parent.is_dir():
        sys.exit(f"missing folder {dest.parent}")
    dest.write_text(content)
    # safety asserts on the generated file
    assert "import Book.Prop" not in content, f"{dest}: still imports flat Book!"
    assert f"theorem {plain} " not in content and f"theorem {plain}:" not in content, \
        f"{dest}: leaked plain {plain}!"
    print(f"  wrote {dest.relative_to(ROOT)}  ({kept} theorem(s))")

def repoint_file(p: pathlib.Path) -> bool:
    lines = p.read_text().splitlines()
    changed = False
    for i, l in enumerate(lines):
        mm = IMPORT_RE.match(l)
        if mm:
            lines[i] = repoint_import(int(mm.group(1)))
            changed = True
    if changed:
        p.write_text("\n".join(lines) + "\n")
    return changed

def main() -> None:
    print("Step 1: generating Book1/PropNN/variants.lean")
    for n in sorted(VARIANT_PROPS):
        gen_variants(n)
    print("Step 2: repointing `import Book.PropM` across Book1/")
    cnt = 0
    for p in sorted(BOOK1.rglob("*.lean")):
        if repoint_file(p):
            cnt += 1
    print(f"  repointed imports in {cnt} file(s)")
    # final sweep: no flat Book.Prop import should remain anywhere under Book1/
    leaks = [str(p.relative_to(ROOT)) for p in BOOK1.rglob("*.lean")
             if any(IMPORT_RE.match(l) for l in p.read_text().splitlines())]
    if leaks:
        sys.exit("LEAK: flat Book.Prop imports still present:\n  " + "\n  ".join(leaks))
    print("Done — no flat Book.Prop imports remain under Book1/. Now: lake build Book1")

if __name__ == "__main__":
    main()
