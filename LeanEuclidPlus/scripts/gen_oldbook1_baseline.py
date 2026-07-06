#!/usr/bin/env python3
"""Generate the isolated OldBook1 / OldBook1Variants baseline from UPSTREAM Book/.

Mirrors the Book1 + Book1Variants structure, but for the pristine upstream proofs, as a
fully self-contained world for benchmarking:

  OldBook1/PropN.lean          -- plain proposition_N (+ any non-primed helper), module OldBook1.PropN
  OldBook1Variants/PropN.lean  -- the primed variants,                          module OldBook1Variants.PropN

Everything stays in namespace Elements.Book1, but the world is IMPORT-ISOLATED: these files
reference only OldBook1.* / OldBook1Variants.* (+ SystemE/Mathlib), never Book/, Book1, or
Book1Variants. Nothing else imports them. So they never share an environment with Book1 and
never collide, and `lake build OldBook1` builds a closed, single-definition world.

Source = the upstream checkout (verified identical to this repo's initial commit f35d0da).
Override with argv[1] if the path differs.

  Run from LeanEuclidPlus/:  python3 scripts/gen_oldbook1_baseline.py [/path/to/LeanEuclid/Book]
  Then:                      lake build OldBook1 && lake build OldBook1Variants
Reversible with git (all output is new files under OldBook1/, OldBook1Variants/, + two roots).
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent          # LeanEuclidPlus/
SRC  = pathlib.Path(sys.argv[1] if len(sys.argv) > 1
                    else "/u/taddmao/code/autoform/LeanEuclid/Book")
OB   = ROOT / "OldBook1"
OBV  = ROOT / "OldBook1Variants"

IMPORT_RE = re.compile(r'^import Book\.Prop(\d+)\s*$')
THM_RE    = re.compile(r'^theorem\s+(\S+?)\s*(?::|$)')

def src_file(n): return SRC / f"Prop{n:02d}.lean"

# pass 0: which upstream props define primed variants?
PROPS = sorted(int(m.group(1)) for p in SRC.glob("Prop*.lean")
               if (m := re.match(r'Prop(\d+)\.lean$', p.name)))
VARIANT_PROPS = set()
for n in PROPS:
    for l in src_file(n).read_text().splitlines():
        mm = THM_RE.match(l)
        if mm and "'" in mm.group(1):
            VARIANT_PROPS.add(n); break

def repoint(m: int) -> str:
    return f"import {'OldBook1Variants' if m in VARIANT_PROPS else 'OldBook1'}.Prop{m:02d}"

def parse(n):
    src = src_file(n).read_text().splitlines()
    end_i = next(i for i, l in enumerate(src) if l.strip() == "end Elements.Book1")
    thms = []
    for i, l in enumerate(src):
        mm = THM_RE.match(l)
        if mm:
            thms.append((i, mm.group(1)))
    imports = []
    for l in src:
        if l.startswith("import "):
            mm = IMPORT_RE.match(l)
            imports.append(repoint(int(mm.group(1))) if mm else l)
    plain, primed = [], []
    for k, (ti, name) in enumerate(thms):
        stop = thms[k + 1][0] if k + 1 < len(thms) else end_i
        (primed if "'" in name else plain).extend(src[ti:stop])
    def trim(b):
        while b and b[-1].strip() == "":
            b.pop()
        return b
    return imports, trim(plain), trim(primed)

def emit(path, imports, body):
    text = "\n".join(imports + ["", "namespace Elements.Book1", ""]
                     + body + ["", "end Elements.Book1", ""])
    path.parent.mkdir(exist_ok=True)
    path.write_text(text)
    for l in text.splitlines():
        m = re.match(r'^import (\S+)', l)
        if m and m.group(1).split('.')[0] in {"Book", "Book1", "Book1Variants"}:
            raise SystemExit(f"{path}: leaked import of the faithful/flat tree: {l!r}")

def main():
    OB.mkdir(exist_ok=True); OBV.mkdir(exist_ok=True)
    for n in PROPS:
        imports, plain, primed = parse(n)
        emit(OB / f"Prop{n:02d}.lean", imports, plain)
        if primed:
            emit(OBV / f"Prop{n:02d}.lean", imports + [f"import OldBook1.Prop{n:02d}"], primed)
    (ROOT / "OldBook1.lean").write_text(
        "\n".join(f"import OldBook1.Prop{n:02d}" for n in PROPS) + "\n")
    (ROOT / "OldBook1Variants.lean").write_text(
        "\n".join(f"import OldBook1Variants.Prop{n:02d}" for n in sorted(VARIANT_PROPS)) + "\n")
    print(f"generated OldBook1/ ({len(PROPS)} props) + OldBook1Variants/ "
          f"({len(VARIANT_PROPS)} variant props): {sorted(VARIANT_PROPS)}")
    print("Now: lake build OldBook1 && lake build OldBook1Variants")

if __name__ == "__main__":
    main()
