#!/usr/bin/env python3
"""Bootstrap Book-1 faithful prop folders: create `Book1/PropNN/Main.lean` statement STUBS from the
flat `Book/PropNN.lean` originals.

Each stub = `import SystemE` + `namespace Elements.Book1` + the VERBATIM `theorem proposition_N`
signature (copied from the flat original) + `:= by sorry`. That is all Phase A needs: `faithful-translate`
reads the signature, and `faithful_map_assemble.py` rewrites the BODY (preserving the signature) into the
`euclid_sentence` map. The stub's `sorry` body is thrown away by assemble; it only has to elaborate.

**Skips** any prop whose `Book1/PropNN/Main.lean` already exists — never clobbers a done prop (e.g. the
Prop06 pilot). Use `--force` to overwrite a stub you intend to regenerate.

Usage:
  python3 scripts/scaffold_stub.py                 # all Book-1 props with a flat original (skips existing)
  python3 scripts/scaffold_stub.py 8 14            # just these prop numbers
  python3 scripts/scaffold_stub.py --dry-run       # report what it would create, write nothing
  python3 scripts/scaffold_stub.py 8 --force       # overwrite an existing Book1/Prop08/Main.lean
"""
import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L

FLAT_DIR = os.path.join(L.BOOK_ROOT, "Book")            # flat Book-1 originals: Book/PropNN.lean
BOOK1_DIR = os.path.join(L.BOOK_ROOT, "Book1")


def extract_signature(src, n):
    """The verbatim `theorem proposition_<n> … ` text, up to (not including) the proof's `:= by`."""
    m = re.search(rf'theorem\s+proposition_{n}\b', src)
    if not m:
        raise L.FaithfulError(f"no `theorem proposition_{n}` in the flat original")
    m2 = re.search(r':=\s*by\b', src[m.start():])
    if not m2:
        raise L.FaithfulError(f"no `:= by` proof delimiter after `theorem proposition_{n}`")
    return src[m.start(): m.start() + m2.start()].rstrip()


def stub_text(sig):
    return f"""import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
{sig} := by
  sorry

end Elements.Book1
"""


def main():
    ap = argparse.ArgumentParser(description="Bootstrap Book-1 PropNN/Main.lean statement stubs.")
    ap.add_argument("props", nargs="*", type=int, help="prop numbers (default: every flat original)")
    ap.add_argument("--dry-run", action="store_true", help="report only; write nothing")
    ap.add_argument("--force", action="store_true", help="overwrite an existing Book1/PropNN/Main.lean")
    args = ap.parse_args()

    nums = args.props or [int(m.group(1))
                          for f in sorted(os.listdir(FLAT_DIR))
                          for m in [re.fullmatch(r"Prop(\d+)\.lean", f)] if m]
    created, skipped, missing, failed = [], [], [], []

    for n in sorted(set(nums)):
        flat = os.path.join(FLAT_DIR, f"Prop{n:02d}.lean")
        target_dir = os.path.join(BOOK1_DIR, f"Prop{n:02d}")
        target = os.path.join(target_dir, "Main.lean")

        if not os.path.exists(flat):
            missing.append(n)
            continue
        if os.path.exists(target) and not args.force:
            skipped.append(n)
            continue
        try:
            sig = extract_signature(open(flat, encoding="utf-8").read(), n)
        except L.FaithfulError as e:
            failed.append((n, str(e)))
            continue

        if args.dry_run:
            created.append(n)
            continue
        os.makedirs(target_dir, exist_ok=True)
        with open(target, "w", encoding="utf-8") as f:
            f.write(stub_text(sig))
        created.append(n)

    verb = "would create" if args.dry_run else "created"
    print(f"{verb} ({len(created)}): " + ", ".join(f"Prop{n:02d}" for n in created) or f"{verb}: none")
    if skipped:
        print(f"skipped, already exist ({len(skipped)}): " + ", ".join(f"Prop{n:02d}" for n in skipped))
    if missing:
        print(f"no flat original ({len(missing)}): " + ", ".join(f"Prop{n:02d}" for n in missing))
    if failed:
        print("FAILED:")
        for n, e in failed:
            print(f"  Prop{n:02d}: {e}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
