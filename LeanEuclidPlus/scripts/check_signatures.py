#!/usr/bin/env python3
"""Proposition-signature guard — snapshot every `theorem proposition_*` SIGNATURE and diff later.

The proposition STATEMENTS (the `theorem proposition_N : ∀ … → …` type, up to the proof `:=`) are
ground truth: faithfulness work re-proves the BODY but must NEVER alter a statement. Agents can get
lazy and quietly weaken a hypothesis or goal to make a proof close. This script lets the human catch
that independently of any agent.

  SNAPSHOT (run BEFORE any agent touches a proof — captures the trusted baseline):
      python3 scripts/check_signatures.py --save

  DIFF (run AFTER agents finish — exits non-zero on any change):
      python3 scripts/check_signatures.py

It scans `Book/Prop*.lean` and `Book2/Prop*.lean` for `theorem proposition_<name> : <type> :=`,
extracts <type> (whitespace-normalized), and stores `{key: {file, line, sig}}` keyed by
`<relfile>::proposition_<name>` (primes and per-file identity unambiguous). All such decls are
`theorem`s that split cleanly on the first top-level `:=` (no `:=` inside the type, no `where`, no
same-line `:= by`) — verified across the 63 declaring files.

Helper lemmas (`helper_*`) are intentionally NOT tracked — they are allowed to change.
"""
import re, sys, os, json

# `theorem proposition_<name> : <type> :=` — name allows trailing primes; type runs to the first
# `:=` (DOTALL so multi-line types match). `:=` never occurs inside these types (verified).
DECL = re.compile(r"theorem\s+(proposition_\w*'*)\s*:(.*?):=", re.DOTALL)

BOOK_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # LeanEuclidPlus/
BASELINE  = os.path.join(BOOK_ROOT, "scripts", "proposition_signatures.json")


def norm(s: str) -> str:
    return " ".join(s.split())


def extract():
    """Return {key -> {file, line, sig}} for every proposition signature under Book/ and Book2/."""
    sigs = {}
    for sub in ("Book", "Book2"):
        d = os.path.join(BOOK_ROOT, sub)
        if not os.path.isdir(d):
            continue
        for fn in sorted(os.listdir(d)):
            if not (fn.startswith("Prop") and fn.endswith(".lean")):
                continue
            path = os.path.join(d, fn)
            rel  = os.path.join(sub, fn)
            src  = open(path, encoding="utf-8").read()
            for m in DECL.finditer(src):
                name = m.group(1)
                line = src.count("\n", 0, m.start()) + 1
                key  = f"{rel}::{name}"
                if key in sigs:
                    print(f"WARNING: duplicate {key} (lines {sigs[key]['line']}, {line})")
                sigs[key] = {"file": rel, "line": line, "sig": norm(m.group(2))}
    return sigs


def save():
    sigs = extract()
    with open(BASELINE, "w", encoding="utf-8") as f:
        json.dump(sigs, f, ensure_ascii=False, indent=2, sort_keys=True)
    print(f"saved {len(sigs)} proposition signatures -> {os.path.relpath(BASELINE, BOOK_ROOT)}")
    return 0


def diff():
    if not os.path.exists(BASELINE):
        print(f"no baseline at {BASELINE}; run `check_signatures.py --save` first")
        return 2
    base = json.load(open(BASELINE, encoding="utf-8"))
    cur  = extract()

    changed = [k for k in base if k in cur and base[k]["sig"] != cur[k]["sig"]]
    removed = [k for k in base if k not in cur]
    added   = [k for k in cur if k not in base]

    for k in sorted(changed):
        print(f"CHANGED  {k}  (now {cur[k]['file']}:{cur[k]['line']})")
        print(f"    baseline: {base[k]['sig']}")
        print(f"    current : {cur[k]['sig']}")
    for k in sorted(removed):
        print(f"REMOVED  {k}  (was {base[k]['file']}:{base[k]['line']})")
    for k in sorted(added):
        print(f"ADDED    {k}  ({cur[k]['file']}:{cur[k]['line']})")

    if changed or removed or added:
        print(f"\nFAIL: {len(changed)} changed, {len(removed)} removed, {len(added)} added "
              f"(statements must not change; new props are fine — re-run --save if intended)")
        return 1
    print(f"OK: all {len(base)} proposition signatures unchanged")
    return 0


def main(argv):
    if argv == ["--save"]:
        return save()
    if not argv:
        return diff()
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
