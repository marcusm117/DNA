#!/usr/bin/env python3
"""The ASSUMPTION PHASE — runs BETWEEN Phase A (sentence map) and Phase B (prove).

For every `-- @assumption ("text", type)` a sentence consumes, this MATERIALIZES an explicit
`have stepK_assumptionN : <type> := by sorry` node, then fires `euclid_finish` at a tight solver cap
at each one, in isolation, to classify it:

  * CLOSES  → the premise was genuinely trivial (conjunct projection, `a=b`↔`b=a`, transitivity …).
              Persist it inline as `:= by euclid_finish` + a `-- @assumption_valid` tag. It becomes a
              finished, node-invisible fact (parse_nodes_in_file skips `euclid_finish`-bodied haves) —
              free work the Phase-B agent never has to prove.
  * NOT     → Euclid asserted a premise he never justified — a REASONING GAP. Persist it as `:= by
    CLOSED    sorry` + `-- @assumption_gap`; Phase B proves it via the normal recursive atom (it is the
              same species as a `step8_eb`-style decomposition sub-node).

The valid/gap classification is recorded in `scripts/assumption_tags.json` (this script's own baseline;
agent-write-denied, mirroring step_signatures.json). `check_steps --save` is NOT touched or re-run.

USAGE  (run from LeanEuclidPlus/):
  python3 scripts/assumptions.py <propdir>              materialize + classify + PERSIST + write tags
  python3 scripts/assumptions.py <propdir> --dry-run    materialize + classify + REPORT only (reverts
                                                          every edit; writes nothing) — the diagnostic

LAYOUT (load-bearing): `_assumptions_above` stops scanning at the first non-`@assumption`/`@args`/blank
line, so the `-- @assumption (…)` comment block MUST stay contiguous directly above the sentence. We
therefore insert the materialized haves ABOVE that block (below the step's construction calls); the wire
(faithful_lib.wired_body) and check_steps keep reading the annotations unchanged.
"""
import argparse
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import faithful_lib as L

# The solver cap that DEFINES "trivial": a genuinely trivial fact closes in <1s of solver time; 3s is
# headroom. Higher would let real gaps close and vanish from the catalog (see the plan's "Why 3s").
CLASSIFY_SOLVER = 3
# A GENEROUS wall so the SOLVER's verdict lands (closes / SAT / unknown) rather than a SIGKILL — the
# build is one Main elaboration (fast, all-sorry) + one ≤3s euclid_finish. Same rationale as smell.
CLASSIFY_WALL = 30

TAGS_FILE = os.path.join(L.BOOK_ROOT, "scripts", "assumption_tags.json")


def classify_target(ok, out):
    """Map a classification build's (ok, output) → a verdict. Distinct from `classify_smell`: that
    demands `not has_sorry`, but here Main ALWAYS carries sorries (every other node is `:= by sorry`),
    so has_sorry is always true. Instead we exploit that the target's `euclid_finish` is the ONLY
    non-sorry tactic in Main — so ANY prove-error is the target's, and a build that SUCCEEDS (ok, only
    sorry WARNINGS) means the target closed.
       'closes' — build ok, target's euclid_finish discharged (other sorries are warnings) ⟹ VALID.
       'wall'   — wall pre-empted the solver: inconclusive, treat as a gap.
       'sat'    — solver returned SAT: the premise is FALSE (a map bug) — surfaced, still a gap.
       'hard'   — `Could not prove`: solver unknown/too-big at the short cap ⟹ genuine Euclid gap.
       'crash'  — euclid_finish CRASHED Lean (native stack trace, no proof verdict) — a TOOLING limit on
                  the goal shape (e.g. superposition `let`/ite maps), NOT a deep Euclid gap; Phase B
                  proves it directly. Deterministic in practice, so tags stay stable.
       'error'  — some other Lean/parse error (e.g. the type doesn't elaborate) — a map bug, gap.
    All non-'closes' verdicts fold into the `gap` tag (Phase B proves them); the distinction is for the
    human report/catalog."""
    o = out or ""
    if "exceeded" in o and "wall clock" in o:
        return "wall"
    if "Prover returned SAT" in o:
        return "sat"
    if "Could not prove" in o:
        return "hard"
    if ok:
        return "closes"
    if "libleanshared.so(" in o or "lean_apply_" in o:      # native crash frames, no proof verdict
        return "crash"
    return "error"


def _block_start_above(src, head_start):
    """Offset of the topmost line of the contiguous `@assumption`/`@args`/blank block directly above the
    sentence head at `head_start` — specifically the start of the topmost `@assumption` line (where we
    insert the haves). Mirrors `_assumptions_above`'s upward scan. None if there is no assumption block."""
    line_start = src.rfind("\n", 0, head_start) + 1
    cursor = line_start
    topmost = None
    while cursor > 0:
        prev_start = src.rfind("\n", 0, cursor - 1) + 1
        line = src[prev_start:cursor - 1]
        if not line.strip():                       # blank — keep scanning
            cursor = prev_start
            continue
        if L.ASSUMPTION_ANNOT.match(line):
            topmost = prev_start
            cursor = prev_start
            continue
        if L.ARGS_ANNOT.match(line):               # (banned in Main, but tolerate while scanning)
            cursor = prev_start
            continue
        break                                       # any other line — block ends here
    return topmost


def sentence_blocks(src):
    """For each `euclid_sentence` carrying `@assumption` annotations: `(name, block_start, indent,
    assumptions)` where `assumptions` = [(text, lean_type, override|None), …] top-to-bottom (from
    `_assumptions_above`), `block_start` is the insertion offset, and `indent` is the leading whitespace
    of the `@assumption` block (so a have inside a nested `habsurd`/`by_cases`/`wlog` block is indented to
    match — a hardcoded 2-space indent would land at the wrong scope and break elaboration). Source order."""
    out = []
    for m in L.SENTENCE_HEAD.finditer(src):
        name = m.group(2)
        assumptions = L._assumptions_above(src, m.start())
        if not assumptions:
            continue
        block_start = _block_start_above(src, m.start())
        if block_start is None:                     # defensive — annotations found but no block start
            continue
        eol = src.find("\n", block_start)
        line = src[block_start:eol if eol != -1 else len(src)]
        indent = line[:len(line) - len(line.lstrip(" "))]
        out.append((name, block_start, indent, assumptions))
    return out


def have_name(sentence_name, i):
    """The materialized node's name: `stepK_assumptionN` (1-based). Obeys the naming law so a gap's
    backing file is `stepK_assumptionN.lean` / `helper_<book>_<prop>_stepK_assumptionN`."""
    return f"{sentence_name}_assumption{i}"


def materialize(src):
    """STEP A: insert one all-`sorry` assumption have above each sentence's `@assumption` block — EVERY
    assumption gets a have, no exceptions (a have redundant with an existing context hyp is fine).
    Bottom-to-top so earlier offsets stay valid. Bodies + valid/gap tags are set later by
    `apply_verdicts` (STEP B); STEP A only stamps the sorry placeholders + the build-check."""
    for name, block_start, indent, assumptions in sorted(sentence_blocks(src), key=lambda b: b[1],
                                                          reverse=True):
        lines = [f"{indent}have {have_name(name, i)} : {typ} := by sorry"
                 for i, (_text, typ, _override) in enumerate(assumptions, 1)]
        src = src[:block_start] + "\n".join(lines) + "\n" + src[block_start:]
    return src


_HAVE_HEAD_RE = re.compile(r'(?m)^([ \t]*)have (\w+_assumption\d+)\b')
_BODY_RE = re.compile(r':=[ \t]*by[ \t]+(?:sorry|euclid_finish)\b')


def apply_verdicts(src, verdicts):
    """STEP B persist — IN PLACE on the current source (preserves any manual frame edit, e.g. a `wlog`
    `Hsym` fix; unlike regenerating from a have-less original). For each materialized
    `have stepK_assumptionN`, set its body (closes → `euclid_finish`, else → `sorry`) and put its
    `-- @assumption_valid`/`-- @assumption_gap` tag directly above it (idempotent). Bottom-to-top so
    offsets stay valid; each edit is at/after its have head, so earlier haves are unaffected."""
    for m in reversed(list(_HAVE_HEAD_RE.finditer(src))):
        indent, hn = m.group(1), m.group(2)
        valid = verdicts.get(hn) == "closes"
        try:
            _typ, sep = L.type_until_assign(src, m.end())
        except L.FaithfulError:
            continue
        bm = _BODY_RE.match(src, sep)
        if not bm:
            continue                                   # not a canonical materialized body — leave it
        src = src[:sep] + (":= by euclid_finish" if valid else ":= by sorry") + src[bm.end():]
        # place the tag comment directly above the have line (idempotent — replace any existing tag)
        line_start = src.rfind("\n", 0, m.start()) + 1
        prev_start = (src.rfind("\n", 0, line_start - 1) + 1) if line_start > 0 else 0
        prev = src[prev_start:line_start - 1] if line_start > 0 else ""
        tag = f"{indent}-- {'@assumption_valid' if valid else '@assumption_gap'}\n"
        if prev.strip() in ("-- @assumption_valid", "-- @assumption_gap"):
            src = src[:prev_start] + tag + src[line_start:]
        else:
            src = src[:line_start] + tag + src[line_start:]
    return src


def classify_all(propdir, book):
    """For each materialized (sorry) have in Main, transiently set it to `euclid_finish` under the 3s
    cap, build Main, classify, revert (atomic via restore_files — one target euclid_finish per build, so
    any prove-error is unambiguously the target's). Returns {have_name: verdict}. Main must already hold
    the all-sorry materialized haves on disk."""
    mf = L.main_file(propdir)
    haves = [nd for nd in L.parse_nodes_in_file(mf, book)
             if nd.kind == "have" and nd.name.split("_assumption")[-1].isdigit()
             and "_assumption" in nd.name]
    verdicts, outputs = {}, {}
    for nd in haves:
        with L.restore_files([mf]):
            src = open(mf, encoding="utf-8").read()
            smelled = L.set_node_state(src, nd, "smell", propdir, book)   # := by euclid_finish
            smelled = L.set_solver_cap(smelled, CLASSIFY_SOLVER)
            open(mf, "w", encoding="utf-8").write(smelled)
            ok, out = L.lake_build(L.target_of(mf), wall=CLASSIFY_WALL)
        v = classify_target(ok, out)
        verdicts[nd.name] = v
        if v != "closes":                                                 # keep the tail for the report
            outputs[nd.name] = "\n".join((out or "").rstrip().splitlines()[-12:])
    return verdicts, outputs


def write_tags(propdir, verdicts, original_src):
    """Merge this prop's per-assumption tags into scripts/assumption_tags.json (keeping other props).
    Record {tag: valid|gap, verdict: <raw>, text, type} per have, keyed prop-rel → have name."""
    rel = os.path.relpath(propdir, L.BOOK_ROOT)
    data = {}
    if os.path.exists(TAGS_FILE):
        try:
            data = json.load(open(TAGS_FILE, encoding="utf-8"))
        except (ValueError, OSError):
            data = {}
    entry = {}
    for name, _bs, _indent, assumptions in sentence_blocks(original_src):
        for i, (text, typ, _override) in enumerate(assumptions, 1):
            hn = have_name(name, i)
            v = verdicts.get(hn, "error")
            entry[hn] = {"tag": "valid" if v == "closes" else "gap", "verdict": v,
                         "text": text, "type": L._norm(typ)}
    data[rel] = entry
    tmp = TAGS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")
    os.replace(tmp, TAGS_FILE)


def report(propdir, verdicts, outputs, original_src, dry_run):
    rel = os.path.relpath(propdir, L.BOOK_ROOT)
    rows = []
    for name, _bs, _indent, assumptions in sentence_blocks(original_src):
        for i, (text, _typ, _override) in enumerate(assumptions, 1):
            hn = have_name(name, i)
            rows.append((hn, verdicts.get(hn, "error"), text))
    n = len(rows)
    valid = [r for r in rows if r[1] == "closes"]
    gaps = [r for r in rows if r[1] != "closes"]
    mode = "DRY-RUN (no writes)" if dry_run else "PERSISTED"
    print(f"[assumptions] {rel} — {mode}")
    print(f"  {n} assumption(s): {len(valid)} valid (auto-closed), {len(gaps)} gap(s).")
    if gaps:
        print(f"  GAPS (Euclid asserted without justification — Phase B must prove):")
        for hn, v, text in gaps:
            flag = {"sat": " [SAT — premise FALSE, likely a MAP BUG]",
                    "crash": " [euclid_finish CRASHED — tooling limit on this goal shape; Phase B proves "
                             "it directly, not a deep Euclid gap]",
                    "error": " [Lean error — check the type / map]",
                    "wall": " [inconclusive at cap]"}.get(v, "")
            print(f"    - {hn} ({v}){flag}: {text}")
            if dry_run and outputs.get(hn):
                for ln in outputs[hn].splitlines():
                    print(f"        | {ln}")
    if valid:
        print(f"  valid: {', '.join(hn for hn, _, _ in valid)}")


def _frame_hint(materialized_src):
    """The fail-closed guidance when STEP A's build breaks (a materialized have broke Main)."""
    if "generalizing" in materialized_src:
        return ("  Likely a `wlog … generalizing` frame: a materialized have before it shifts the "
                "generated `Hsym` arity. Manually add the (redundant) extra argument to the reduction "
                "(the `exact Hsym …` call + `swapfig`'s `obtain` if needed) — do NOT delete the have — "
                "then re-run with `--tag-only`.")
    return ("  A materialized have broke Main's build. Fix the frame to accept it (do NOT delete the "
            "have), then re-run with `--tag-only`.")


def _step_b(propdir, book, original, dry_run):
    """STEP B — classify the already-materialized haves, then persist IN PLACE + tag (or revert if
    dry_run). Requires an intact frame (STEP A build passed, or the human fixed it)."""
    mf = L.main_file(propdir)
    verdicts, outputs = classify_all(propdir, book)
    disk = open(mf, encoding="utf-8").read()                 # materialized haves (+ any manual frame fix)
    if dry_run:
        open(mf, "w", encoding="utf-8").write(original)      # revert — pure diagnostic
    else:
        open(mf, "w", encoding="utf-8").write(apply_verdicts(disk, verdicts))
        write_tags(propdir, verdicts, disk)
    report(propdir, verdicts, outputs, disk, dry_run)
    return 0


def run(propdir, dry_run=False, tag_only=False):
    book = L.book_num(propdir)
    mf = L.main_file(propdir)
    rel = os.path.relpath(propdir, L.BOOK_ROOT)
    original = open(mf, encoding="utf-8").read()

    # PRECONDITION: a FRESH Phase-A map — every sentence `:= by sorry`, no helper/step imports. A
    # wired/post-Phase-B Main is the wrong state: materializing into an already-proven frame is
    # meaningless and, near a `wlog`, corrupts it. Abort loudly.
    pipeline_imps = L.pipeline_imports(original, propdir)
    wired = [nd for nd in L.parse_nodes_in_file(mf, book)
             if nd.kind == "sentence" and nd.state != "sorry"]
    if pipeline_imps or wired:
        why = []
        if pipeline_imps:
            why.append(f"helper/step imports present ({', '.join(pipeline_imps)})")
        if wired:
            why.append(f"{len(wired)} sentence body/ies already wired (e.g. {wired[0].name})")
        print(f"ERROR: {rel} is not in the fresh Phase-A dev state ({'; '.join(why)}). Run the assumption "
              f"phase BETWEEN the map and Phase B — sentences all `:= by sorry`, no helper imports. "
              f"(Unwire with `wire_main.py --unwire` if already wired.)")
        return 2

    if not sentence_blocks(original):
        print(f"[assumptions] {rel} — no @assumption annotations; nothing to do.")
        return 0

    # --tag-only: STEP B only — the haves are already materialized (+ frame fixed by hand).
    if tag_only:
        present = {m.group(2) for m in _HAVE_HEAD_RE.finditer(original)}
        if not present:
            print(f"ERROR: --tag-only but no `stepK_assumptionN` haves in {rel}. Run `assumptions.py "
                  f"{rel}` first (STEP A materializes + build-checks).")
            return 2
        try:
            return _step_b(propdir, book, original, dry_run=False)
        except BaseException:
            open(mf, "w", encoding="utf-8").write(original)
            raise

    # STEP A — materialize the all-sorry haves, then build-check Main.
    open(mf, "w", encoding="utf-8").write(materialize(original))
    materialized = open(mf, encoding="utf-8").read()
    try:
        ok, out = L.lake_build(L.target_of(mf), wall=L.main_wall(propdir))
    except BaseException:
        open(mf, "w", encoding="utf-8").write(original)      # crash → revert
        raise

    if not ok:
        if dry_run:
            open(mf, "w", encoding="utf-8").write(original)  # diagnostic → revert
            print(f"[assumptions] {rel} — DRY-RUN: STEP A build FAILED (materialization breaks Main). "
                  f"Reverted.")
        else:
            print(f"[assumptions] {rel} — STEP A build FAILED: the materialized haves broke Main's build. "
                  f"Sorry haves LEFT IN PLACE (fail-closed) for you to fix.")   # do NOT revert
        print(_frame_hint(materialized))
        tail = "\n".join((out or "").rstrip().splitlines()[-12:])
        for ln in tail.splitlines():
            print(f"    | {ln}")
        return 1

    # STEP A passed → STEP B (auto).
    try:
        return _step_b(propdir, book, original, dry_run)
    except BaseException:
        open(mf, "w", encoding="utf-8").write(original)
        raise


def main():
    ap = argparse.ArgumentParser(description="The Assumption Phase: materialize a have per @assumption, "
                                             "build-check, then classify + tag valid/gap.")
    ap.add_argument("propdir", help="Proposition directory, e.g. Book1/Prop01")
    ap.add_argument("--dry-run", action="store_true",
                    help="STEP A + STEP B but revert every edit, write nothing (pure diagnostic)")
    ap.add_argument("--tag-only", action="store_true",
                    help="STEP B only: classify + tag already-materialized haves (after a manual frame "
                         "fix). Skips materialize + build-check.")
    args = ap.parse_args()
    try:
        propdir = L.propdir_of(args.propdir)
    except L.FaithfulError as e:
        print(f"ERROR: {e}")
        return 2
    with L.prop_lock(propdir):
        return run(propdir, dry_run=args.dry_run, tag_only=args.tag_only)


if __name__ == "__main__":
    sys.exit(main())
