#!/usr/bin/env python3
"""Step-claim guard — snapshot the approved `euclid_sentence` CLAIM TYPES and diff later.

After a Phase-A sentence map is HUMAN-APPROVED, the `step_n : <claim type>` of each `euclid_sentence`
is frozen: Phases B/C may not change it, and an agent must never silently WEAKEN a claim (drop a
conjunct, flip an equality to something trivially true) to make a proof easier. The sentence TEXTS
and locators are already guarded by `check_faithful.py` (criterion 1 / contiguity); the one thing it
does NOT guard is the claim TYPE. This script fills that gap, mirroring `check_signatures.py`.

Per-prop incremental baseline (you approve Phase A one prop at a time):

  SNAPSHOT (run right AFTER you approve a prop's sentence map):
      python3 scripts/check_steps.py --save Book2/Prop03/Main.lean
  Merges that prop's {locator -> claim type} into scripts/step_signatures.json (other props kept).

  DIFF (run anytime — exits non-zero on any change to an approved claim):
      python3 scripts/check_steps.py                  # all recorded props
      python3 scripts/check_steps.py Book2/Prop03/Main.lean # just one

Changing a claim type is ALLOWED — but never SILENTLY: the diff flags CHANGED/ADDED/REMOVED so the
human adjudicates (and re-runs --save once the new map is approved). Source-based, no build, instant.
Only `euclid_sentence` (logical) steps carry a claim; the structural intro/conclude sentences don't.
"""
import re, sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import faithful_lib as _fl

BOOK_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # LeanEuclidPlus/
BASELINE  = os.path.join(BOOK_ROOT, "scripts", "step_signatures.json")

# `euclid_sentence "loc" "text" (name :` — we capture loc + name, then balance-scan the type.
HEAD = re.compile(
    r'euclid_sentence\s*"((?:[^"\\]|\\.)*)"\s*"(?:[^"\\]|\\.)*"\s*\(\s*(\w+)\s*:')


def norm(s: str) -> str:
    return " ".join(s.split())


def balanced_type(src: str, start: int):
    """`start` is the index just AFTER the `:` of `(name : type)`. Scan to the matching close paren
    of the ALREADY-OPEN annotation paren (depth starts at 1), respecting nested parens and skipping
    string literals. Return (type_text, index_after_close)."""
    depth, i, n = 1, start, len(src)
    while i < n:
        c = src[i]
        if c == '"':                       # skip a string literal (types rarely have them, be safe)
            i += 1
            while i < n and src[i] != '"':
                i += 2 if src[i] == '\\' else 1
            i += 1
            continue
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                return src[start:i], i + 1
        i += 1
    return src[start:], n                  # unbalanced (shouldn't happen in valid source)


def extract_file(path: str):
    """Return {loc -> {file, line, name, claim, assumptions?}} for every euclid_sentence in one .lean
    file. `assumptions` is present (and non-empty) only when the node has `-- @assumption` annotations;
    each entry is `{"text": str, "type": str}` or `{"text": str, "type": str, "override": str}`.
    `@assumption` types are Phase-A's reasoning map, frozen at the gate ALONGSIDE the claim type: under
    the Assumption Phase they are first-class, so drift against this baseline is a HARD FAIL (not a
    warning) — an intended change (a bad assumption dropped/retyped) must be re-approved and re-saved
    with `--save`, exactly like a claim-type change."""
    raw = open(path, encoding="utf-8").read()
    rel = os.path.relpath(path, BOOK_ROOT)
    # Use faithful_lib to get Node objects (with .assumptions populated) for assumption data.
    try:
        book = _fl.book_num(_fl.propdir_of(os.path.dirname(path)))
        nodes_by_loc = {nd.loc: nd
                        for nd in _fl.parse_nodes_in_file(path, book)
                        if nd.kind == "sentence"}
    except _fl.FaithfulError:
        nodes_by_loc = {}
    out = {}
    for m in HEAD.finditer(raw):
        loc, name = m.group(1), m.group(2)
        claim, _ = balanced_type(raw, m.end())
        line = raw.count("\n", 0, m.start()) + 1
        entry = {"file": rel, "line": line, "name": name, "claim": norm(claim)}
        nd = nodes_by_loc.get(loc)
        if nd and nd.assumptions:
            assump_list = []
            for text, atype, override in nd.assumptions:
                a = {"text": text, "type": norm(atype)}
                if override:
                    a["override"] = override
                assump_list.append(a)
            entry["assumptions"] = assump_list
        out[loc] = entry
    return out


def resolve(arg: str) -> str:
    """Accept a path relative to LeanEuclidPlus/ or absolute; return absolute."""
    return arg if os.path.isabs(arg) else os.path.join(BOOK_ROOT, arg)


def load_baseline():
    return json.load(open(BASELINE, encoding="utf-8")) if os.path.exists(BASELINE) else {}


def save(prop_arg: str):
    path = resolve(prop_arg)
    if not os.path.exists(path):
        print(f"no such file: {prop_arg}")
        return 2
    steps = extract_file(path)
    if not steps:
        print(f"no euclid_sentence steps found in {prop_arg} — nothing saved")
        return 2
    base = load_baseline()
    rel = os.path.relpath(path, BOOK_ROOT)
    base = {k: v for k, v in base.items() if v.get("file") != rel}  # drop old entries for this file
    base.update(steps)                     # merge: this prop's locators replace/add; others untouched
    with open(BASELINE, "w", encoding="utf-8") as f:
        json.dump(base, f, ensure_ascii=False, indent=2, sort_keys=True)
    n_assumps = sum(len(v.get("assumptions") or []) for v in steps.values())
    print(f"approved {len(steps)} step claim(s)"
          + (f" + {n_assumps} @assumption(s)" if n_assumps else "")
          + f" from {os.path.relpath(path, BOOK_ROOT)} -> {os.path.relpath(BASELINE, BOOK_ROOT)}")
    for loc in sorted(steps):
        s = steps[loc]
        print(f"    {loc}  {s['name']} : {s['claim']}")
        for a in s.get("assumptions") or []:
            ov = f"  [{a['override']}]" if a.get("override") else ""
            print(f"        @assumption  \"{a['text']}\" → {a['type']}{ov}")
    return 0


def diff(prop_arg: str = None):
    print("[check_steps] verifying approved Phase-A claim types are unchanged "
          "(approve/update with: check_steps.py --save Book<N>/Prop<NN>.lean)")
    base = load_baseline()
    if not base:
        print(f"no baseline at {BASELINE}; approve a prop first with `--save <Prop>.lean`")
        return 2

    # Which locators to check: those in the baseline, optionally restricted to one prop's file.
    if prop_arg:
        rel = os.path.relpath(resolve(prop_arg), BOOK_ROOT)
        keys = [k for k, v in base.items() if v["file"] == rel]
        if not keys:
            print(f"no approved steps recorded for {rel} (run --save after approving its Phase A)")
            return 2
        cur = extract_file(resolve(prop_arg))
    else:
        keys = list(base.keys())
        cur = {}
        for f in sorted({v["file"] for v in base.values()}):
            p = os.path.join(BOOK_ROOT, f)
            if os.path.exists(p):
                cur.update(extract_file(p))

    changed = [k for k in keys if k in cur and base[k]["claim"] != cur[k]["claim"]]
    removed = [k for k in keys if k not in cur]
    added   = [k for k in cur if k not in base]   # locators present in source but never approved

    # Also check assumption annotations: saved types must still appear in current source annotations.
    assump_changed = []
    for k in keys:
        if k not in cur:
            continue
        saved_assumps = base[k].get("assumptions") or []
        cur_assumps   = cur[k].get("assumptions") or []
        cur_types = {norm(a["type"]) for a in cur_assumps}
        for a in saved_assumps:
            if norm(a["type"]) not in cur_types:
                assump_changed.append((k, a["type"], a.get("text", "")))

    for k in sorted(changed):
        print(f"CHANGED  {k}  ({cur[k]['file']}:{cur[k]['line']})")
        print(f"    approved: {base[k]['claim']}")
        print(f"    current : {cur[k]['claim']}")
    for k in sorted(removed):
        print(f"REMOVED  {k}  (approved in {base[k]['file']}:{base[k]['line']})")
    for k in sorted(added):
        print(f"ADDED    {k}  ({cur[k]['file']}:{cur[k]['line']}) — not in approved baseline")
    # @assumption drift is now a HARD FAIL (#2a): under the assumption phase, assumptions are first-class
    # PROVEN obligations — every one must stay supplied to its sentence's claim, so the agent may NOT
    # drop or retype one after approval. (Reverses the old non-blocking latitude.)
    for k, atype, text in sorted(assump_changed):
        print(f"DRIFT (assumption)  {k}: frozen annotation type \"{atype}\" (\"{text}\") no longer "
              f"appears in source — restore it, or (if the map genuinely changed and was re-approved) "
              f"re-run `--save`.")

    if changed or removed or added or assump_changed:
        print(f"\nFAIL: {len(changed)} changed, {len(removed)} removed, {len(added)} added, "
              f"{len(assump_changed)} assumption drift. Claim types AND assumptions are frozen after "
              f"Phase-A approval — if a change is intended, get it re-approved and re-run `--save`.")
        return 1
    print(f"OK: all {len(keys)} approved step claim(s) + assumptions unchanged"
          + (f" in {os.path.relpath(resolve(prop_arg), BOOK_ROOT)}" if prop_arg else ""))
    return 0


def main(argv):
    if len(argv) == 2 and argv[0] == "--save":
        return save(argv[1])
    if len(argv) == 1 and not argv[0].startswith("--"):
        return diff(argv[0])
    if not argv:
        return diff()
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
