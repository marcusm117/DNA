#!/usr/bin/env python3
"""Proposition-signature guard — snapshot every `theorem proposition_*` SIGNATURE and diff later.

The proposition STATEMENTS (the `theorem proposition_N : ∀ … → …` type, up to the proof `:=`) are
ground truth: faithfulness work re-proves the BODY but must NEVER alter a statement. Agents can get
lazy and quietly weaken a hypothesis or goal to make a proof close. This script lets the human catch
that independently of any agent.

  SNAPSHOT ALL (run BEFORE any agent touches a proof — captures the trusted baseline):
      python3 scripts/check_signatures.py --save

  SNAPSHOT A SUBSET (re-save just the matching signatures, leave every other baseline entry intact):
      python3 scripts/check_signatures.py --save Prop14        # substring: Prop14 in every book
      python3 scripts/check_signatures.py --save Book3         # whole book 3
      python3 scripts/check_signatures.py --save Book3/11-16    # props 11..16 in book 3
      python3 scripts/check_signatures.py --save Book3/11-      # prop 11 to the end of book 3
      python3 scripts/check_signatures.py --save Book3/11       # just prop 11 (Book3/Prop11 also ok)
  The argument is either a book/range SPEC or a plain SUBSTRING (see FILTER below). Any baseline entry
  matching the filter but no longer present in the sources is REMOVED; non-matching entries are
  untouched. Use this after you've (intentionally, human-authorised) established or changed a prop's
  statement, instead of re-snapshotting the whole baseline.

  DIFF ALL (run AFTER agents finish — exits non-zero on any change):
      python3 scripts/check_signatures.py

  DIFF A SUBSET (same FILTER grammar as --save; checks only the matching keys):
      python3 scripts/check_signatures.py Book3/Prop11   # exit 0 if just Prop11 is unchanged
      python3 scripts/check_signatures.py Book3/11-16     # check props 11..16 of book 3
  A single bare (non-flag) argument scopes the diff. Exits 0 if the matching signatures equal the
  baseline, 1 on a change/add/remove within scope, 2 if the filter matches nothing on either side.

  FILTER grammar (used by both --save <F> and the bare-argument diff):
      BookN            whole book N               (book 1 = both flat `Book/` and `Book1/`)
      BookN/LO-HI      props LO..HI in book N      (Prop prefix optional: BookN/PropLO also works)
      BookN/LO-        props LO..end in book N
      BookN/LO         just prop LO in book N
      <anything else>  plain SUBSTRING of the key `<relfile>::proposition_<name>` (e.g. `Prop14`)

It scans `Book/Prop*.lean` (Book 1, flat) plus the foldered layouts `Book1/Prop*/Main.lean`,
`Book2/Prop*/Main.lean`, and `Book3/Prop*/Main.lean` for `theorem proposition_<name> : <type> :=`,
extracts <type> (whitespace-normalized), and stores `{key: {file, line, sig}}` keyed by
`<relfile>::proposition_<name>` (primes and per-file identity unambiguous). All such decls are
`theorem`s that split cleanly on the first top-level `:=` (no `:=` inside the type, no `where`, no
same-line `:= by`) — comments (incl. mid-signature `--` notes, as in Book3) are blanked first.

Helper lemmas (`helper_*`) are intentionally NOT tracked — they are allowed to change.
"""
import re, sys, os, json, glob

# `theorem proposition_<name> : <type> :=` — name allows trailing primes; type runs to the first
# `:=` (DOTALL so multi-line types match). `:=` never occurs inside these types (verified).
DECL = re.compile(r"theorem\s+(proposition_\w*'*)\s*:(.*?):=", re.DOTALL)

BOOK_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # LeanEuclidPlus/
BASELINE  = os.path.join(BOOK_ROOT, "scripts", "proposition_signatures.json")


def strip_comments(src: str) -> str:
    """Blank out Lean `--` line and nested `/- … -/` block comments (replace with spaces, keep
    newlines) so a COMMENTED-OUT `theorem proposition_…` is not matched. Mirrors check_faithful.py."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        two = src[i:i+2]
        if depth == 0 and two == "--":
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
            continue
        if two == "/-":
            depth += 1; out.append("  "); i += 2; continue
        if two == "-/" and depth > 0:
            depth -= 1; out.append("  "); i += 2; continue
        if depth > 0:
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        out.append(src[i]); i += 1
    return "".join(out)


def norm(s: str) -> str:
    return " ".join(s.split())


# A filter argument is either a plain SUBSTRING (matched against the key) or a book/range SPEC:
#   Book3            whole book 3
#   Book3/11-16      props 11..16 in book 3
#   Book3/11-        props 11..end in book 3
#   Book3/11         just prop 11 in book 3        (Prop prefix optional: Book3/Prop11 same)
# Anything not matching this grammar (e.g. `Prop14`, a bare name) falls back to substring matching.
# Book 1 lives in BOTH `Book/` (flat) and `Book1/`; a `Book1…` spec matches both (compared by number).
RANGE_RE = re.compile(r"^(Book\d*)(?:/(?:Prop)?(\d+)(-)?(\d+)?)?$")


def _book_num(prefix: str) -> int:
    """'Book' or 'Book1' -> 1, 'Book2' -> 2, 'Book3' -> 3."""
    d = prefix[4:]
    return int(d) if d else 1


def _key_book_prop(key: str):
    """(book_number, prop_number) for a signature key, or None if it isn't a Prop file key."""
    m = re.match(r"^(Book\d*)/Prop(\d+)", key)
    return (_book_num(m.group(1)), int(m.group(2))) if m else None


def parse_filter(f: str):
    """Return a predicate key->bool for a filter argument (range spec, else substring)."""
    m = RANGE_RE.match(f)
    if not m:
        return lambda k: f in k
    book = _book_num(m.group(1))
    lo, dash, hi = m.group(2), m.group(3), m.group(4)
    if lo is None:                                   # whole book
        return lambda k: (_key_book_prop(k) or (None,))[0] == book
    lo = int(lo)
    if dash is None:                                 # single prop
        return lambda k: _key_book_prop(k) == (book, lo)
    hi = int(hi) if hi is not None else None         # range lo-hi or lo-
    def pred(k):
        bp = _key_book_prop(k)
        return bp is not None and bp[0] == book and bp[1] >= lo and (hi is None or bp[1] <= hi)
    return pred


def _prop_files():
    """Every proposition source file, flat OR folder layout, relative to BOOK_ROOT:
      Book 1 (flat):    Book/Prop*.lean
      Book 1 (folders): Book1/Prop*/Main.lean
      Book 2 (folders): Book2/Prop*/Main.lean   (post-refactor)
      Book 2 (flat):    Book2/Prop*.lean         (any not-yet-migrated, for safety)
      Book 3 (folders): Book3/Prop*/Main.lean
    De-duplicated, sorted."""
    pats = ["Book/Prop*.lean", "Book1/Prop*/Main.lean",
            "Book2/Prop*/Main.lean", "Book2/Prop*.lean",
            "Book3/Prop*/Main.lean"]
    rels = []
    for pat in pats:
        for path in glob.glob(os.path.join(BOOK_ROOT, pat)):
            rels.append(os.path.relpath(path, BOOK_ROOT))
    return sorted(set(rels))


def extract():
    """Return {key -> {file, line, sig}} for every proposition signature (flat or folder layout)."""
    sigs = {}
    for rel in _prop_files():
        path = os.path.join(BOOK_ROOT, rel)
        src  = strip_comments(open(path, encoding="utf-8").read())
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


def diff(prop_filter=None):
    """Diff current signatures against the baseline. If prop_filter is given, restrict BOTH sides to
    keys containing it as a substring (e.g. 'Book3/Prop11') — a scoped check of just that prop."""
    if not os.path.exists(BASELINE):
        print(f"no baseline at {BASELINE}; run `check_signatures.py --save` first")
        return 2
    base = json.load(open(BASELINE, encoding="utf-8"))
    cur  = extract()

    if prop_filter is not None:
        pred = parse_filter(prop_filter)
        base = {k: v for k, v in base.items() if pred(k)}
        cur  = {k: v for k, v in cur.items()  if pred(k)}
        if not base and not cur:
            print(f"no signatures match '{prop_filter}' in either baseline or sources")
            return 2

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

    scope = f" matching '{prop_filter}'" if prop_filter is not None else ""
    if changed or removed or added:
        print(f"\nFAIL: {len(changed)} changed, {len(removed)} removed, {len(added)} added "
              f"(statements must not change; new props are fine — re-run --save if intended)")
        return 1
    print(f"OK: all {len(base)} proposition signatures{scope} unchanged")
    return 0


def save_prop(prop_filter):
    """Re-save signatures matching prop_filter (substring or book/range spec), keep the rest."""
    pred = parse_filter(prop_filter)
    if os.path.exists(BASELINE):
        sigs = json.load(open(BASELINE, encoding="utf-8"))
    else:
        sigs = {}
    cur = extract()
    removed = [k for k in list(sigs) if pred(k) and k not in cur]
    for k in removed:
        del sigs[k]
    updated = 0
    for k, v in cur.items():
        if pred(k):
            sigs[k] = v
            updated += 1
    with open(BASELINE, "w", encoding="utf-8") as f:
        json.dump(sigs, f, ensure_ascii=False, indent=2, sort_keys=True)
    print(f"updated {updated} signature(s) matching '{prop_filter}', removed {len(removed)} "
          f"-> {os.path.relpath(BASELINE, BOOK_ROOT)}")
    return 0


def main(argv):
    if argv == ["--save"]:
        return save()
    if len(argv) == 2 and argv[0] == "--save":
        return save_prop(argv[1])
    if not argv:
        return diff()
    if len(argv) == 1 and not argv[0].startswith("-"):
        return diff(argv[0])
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
