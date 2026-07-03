#!/usr/bin/env python3
"""The ASSUMPTION PHASE — runs BETWEEN Phase A (sentence map) and Phase B (prove).

For every `-- @assumption ("text", type)` a sentence consumes, this MATERIALIZES an explicit
`have stepK_assumptionN : <type> := by sorry` node (STEP A), then classifies each by trying a LADDER of
tactics in order (STEP B), CHEAPEST/most-trivial first, and PERSISTING the FIRST one that closes it:

  LEVEL  TACTIC              means the premise is …
    1    rfl                 a definitional identity (e.g. `|(a─f)| = |(a─f)|` — "AF is common")
    2    assumption          literally a hypothesis already in context (a restated given)
    3    simp (zetaDelta)    closable by unfolding local `let`s + simp — the superposition-map
                             coincidences (`lineImg AB = DE`), which crash bare euclid_finish
    4    linarith            linear arithmetic over lengths (Common Notions: equals ± equals …)
    5    nlinarith           nonlinear arithmetic (products / areas)
    6    euclid_finish       needs the full geometric SMT offload (z3), at a 30s solver cap
   gap   (none closed)       a genuine REASONING GAP — Euclid asserted it with no mechanical justification

  * CLOSED at level K → persist that tactic inline as `:= by <tactic>` + a `-- @assumption_valid` tag.
    It becomes a finished, node-invisible fact (Phase B never re-proves it). The rung K is a GRADED
    triviality measure: higher = less trivial. rfl/assumption/linarith/nlinarith run NO external solver
    (deterministic; immune to the SMT-portfolio flake AND the `simp_all` maxRecDepth loop). A `linarith`/
    `nlinarith` winner also gets `import Mathlib.Tactic.Linarith` added to Main permanently.
  * GAP (nothing closed it) → persist `:= by sorry` + `-- @assumption_gap`; Phase B proves it via the
    normal recursive atom (same species as a `step8_eb`-style decomposition sub-node).

The `tag` (valid|gap — what the enforcers read), plus `closed_by` (the winning tactic), `level` (the rung,
1–5, or null on gap), and `verdict` are recorded per have in `scripts/assumption_tags.json` (this script's
own baseline; agent-write-denied, mirroring step_signatures.json). `check_steps --save` is NOT re-run.
After persisting, the COMBINED Main is re-built once (each ladder probe only verified ONE have in
isolation); if that fails the run STOPS, tags are NOT written, and the Main is left for review.

USAGE  (run from LeanEuclidPlus/):
  python3 scripts/assumptions.py <propdir>              BARE run = materialize (STEP A) + build-check +
                                                          classify (STEP B) + persist + write tags, ALWAYS
                                                          from the current `-- @assumption` comments. If the
                                                          prop is ALREADY materialized, it RE-MATERIALIZES
                                                          FROM SCRATCH — deletes every existing have and
                                                          re-adds from the current comments (so an added /
                                                          removed / retyped assumption is reflected) — after
                                                          a y/N confirm. (A fresh prop has no haves ⟹ no
                                                          prompt; a non-TTY "no" answer aborts safely.)
  python3 scripts/assumptions.py <propdir> --tag-only   STEP B ONLY on already-materialized haves: re-run
                                                          the ladder + re-tag, skipping STEP A (no delete,
                                                          no prompt). Use after a manual frame fix (a
                                                          `wlog`/`Hsym` break), or to re-classify the SAME
                                                          have set with an updated ladder. Errors if no
                                                          haves are materialized yet.
  python3 scripts/assumptions.py <propdir> --dry-run    materialize + classify + REPORT only (reverts every
                                                          edit; writes nothing) — the diagnostic.

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

# The classification LADDER: cheap terminal closers first (most trivial), euclid_finish last (full
# geometric SMT offload). The FIRST rung that closes an assumption is PERSISTED as its body, and its
# 1-based rung number is recorded (a graded triviality measure — post-processable from the tags). The
# non-euclid_finish rungs run NO external solver: deterministic, and immune to BOTH the SMT-portfolio
# launch flake AND the `simp_all` maxRecDepth loop that made trivia (e.g. `|af|=|af|`) fall through to a
# slow/failing euclid_finish. Only the euclid_finish rung offloads to z3.
#   The `simp (zetaDelta)` rung is GOAL-ONLY (not simp_all, so no cyclic-rewrite loop) and delta-unfolds
#   LOCAL `let`s — it closes the superposition-map coincidences (`let lineImg := fun L => if L = AB then
#   DE …`; `lineImg AB = DE` unfolds → `DE = DE`). Those crash bare `euclid_finish` (its SMT translator
#   dies on the `let`/`ite`/lambda shape), so this rung turns those crash-gaps into valid. Context-
#   dependent map claims (e.g. `ptImg b = e` where `b'=e` is an earlier fact) still need the context and
#   stay gaps for Phase B — correctly.
# Each rung: (tactic, solver_cap | None, required_import | None).
LADDER = [
    ("rfl",                                    None, None),
    ("assumption",                             None, None),
    ("simp (config := { zetaDelta := true })", None, None),
    ("linarith",                               None, "Mathlib.Tactic.Linarith"),
    ("nlinarith",                              None, "Mathlib.Tactic.Linarith"),
    ("euclid_finish",                          30,   None),
]
# A GENEROUS wall for the cheap (no-solver) rungs — one Main elaboration + a fast tactic. The
# euclid_finish rung uses its solver_cap + headroom so the SOLVER's verdict lands rather than a SIGKILL.
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

# Inverse of `materialize` (+ the STEP-B tag): a `-- @assumption_valid`/`@assumption_gap` tag line, and a
# single-line `have stepK_assumptionN … := by …`. NOT the `-- @assumption ("…", type)` comment (that has a
# space+`(`, not the `_valid`/`_gap` suffix) — those are the source of truth and MUST survive a strip.
_ASSUMPTION_TAG_RE  = re.compile(r'(?m)^[ \t]*--[ \t]*@assumption_(?:valid|gap)[ \t]*\r?\n')
_ASSUMPTION_HAVE_RE = re.compile(r'(?m)^[ \t]*have \w+_assumption\d+\b[^\n]*\r?\n')


def strip_materialized(src):
    """Remove every materialized assumption have + its valid/gap tag, leaving the `-- @assumption (…)`
    comment blocks intact. Lets a bare run RE-materialize from scratch (reflecting added/removed/retyped
    assumptions) without duplicating — the robust inverse of the old auto-skip."""
    return _ASSUMPTION_HAVE_RE.sub('', _ASSUMPTION_TAG_RE.sub('', src))


def _confirm(prompt):
    """Interactive y/N. A non-`y` answer — including EOF / a non-TTY stdin — returns False (safe default:
    abort, so a scripted/headless bare re-run never destructively re-materializes without a human `y`)."""
    try:
        return input(prompt).strip().lower() in ("y", "yes")
    except EOFError:
        return False


def _set_have_body(src, name, tactic):
    """Return `src` with `have <name>`'s single-line body replaced by `:= by <tactic>` (assumption haves
    are always single-line `have … := by …`)."""
    for m in _HAVE_HEAD_RE.finditer(src):
        if m.group(2) != name:
            continue
        _typ, sep = L.type_until_assign(src, m.end())
        eol = src.find("\n", sep)
        eol = len(src) if eol == -1 else eol
        return src[:sep] + f":= by {tactic}" + src[eol:]
    raise L.FaithfulError(f"assumption have '{name}' not found for body-set")


def _add_import(src, module):
    """Insert `import <module>` after the last top-of-file import line, if absent (idempotent). Keeps it
    before any `set_option`/`namespace`, so it stays a legal import position."""
    if re.search(r'(?m)^import ' + re.escape(module) + r'\s*$', src):
        return src
    imports = list(re.finditer(r'(?m)^import .*$', src))
    if not imports:
        return f"import {module}\n" + src
    pos = imports[-1].end()
    return src[:pos] + f"\nimport {module}" + src[pos:]


def apply_verdicts(src, results):
    """STEP B persist — IN PLACE on the current source (preserves any manual frame edit, e.g. a `wlog`
    `Hsym` fix). For each materialized `have stepK_assumptionN`, set its body to the WINNING ladder tactic
    (valid) or `:= by sorry` (gap), and put its `-- @assumption_valid`/`-- @assumption_gap` tag directly
    above it (idempotent). Any import a winning tactic needs (e.g. `Mathlib.Tactic.Linarith`) is added to
    Main permanently at the end. Bottom-to-top so offsets stay valid; each body edit is at/after its have
    head, so earlier haves are unaffected."""
    needed_imports = set()
    for m in reversed(list(_HAVE_HEAD_RE.finditer(src))):
        indent, hn = m.group(1), m.group(2)
        rec = results.get(hn) or {}
        valid = rec.get("status") == "valid"
        body = (rec.get("tactic") or "euclid_finish") if valid else "sorry"
        if valid and rec.get("import"):
            needed_imports.add(rec["import"])
        try:
            _typ, sep = L.type_until_assign(src, m.end())
        except L.FaithfulError:
            continue
        eol = src.find("\n", sep)
        eol = len(src) if eol == -1 else eol
        src = src[:sep] + f":= by {body}" + src[eol:]
        # place the tag comment directly above the have line (idempotent — replace any existing tag)
        line_start = src.rfind("\n", 0, m.start()) + 1
        prev_start = (src.rfind("\n", 0, line_start - 1) + 1) if line_start > 0 else 0
        prev = src[prev_start:line_start - 1] if line_start > 0 else ""
        tag = f"{indent}-- {'@assumption_valid' if valid else '@assumption_gap'}\n"
        if prev.strip() in ("-- @assumption_valid", "-- @assumption_gap"):
            src = src[:prev_start] + tag + src[line_start:]
        else:
            src = src[:line_start] + tag + src[line_start:]
    for imp in sorted(needed_imports):
        src = _add_import(src, imp)
    return src


def classify_all(propdir, book):
    """For each materialized assumption have, probe the LADDER in order: transiently set its body to each
    rung's tactic (adding that rung's import + solver cap if any), build Main, and stop at the FIRST rung
    that closes. All edits are reverted per-rung via restore_files. Selects haves by NAME (not the node
    model), so a have already carrying a closer body from a prior run is RE-probed (not skipped).

    Returns ({have_name: record}, {have_name: output_tail}) where record =
    {status: 'valid'|'gap', tactic, level, import, verdict}: tactic/level/import identify the winning rung
    (None on gap); verdict is the last rung's raw verdict (informs the report flag on gaps)."""
    mf = L.main_file(propdir)
    names = [m.group(2) for m in _HAVE_HEAD_RE.finditer(open(mf, encoding="utf-8").read())]
    results, outputs = {}, {}
    for name in names:
        rec = {"status": "gap", "tactic": None, "level": None, "import": None, "verdict": "error"}
        last_out = ""
        for level, (tac, cap, imp) in enumerate(LADDER, 1):
            with L.restore_files([mf]):
                src = _set_have_body(open(mf, encoding="utf-8").read(), name, tac)
                if imp:
                    src = _add_import(src, imp)
                if cap is not None:
                    src = L.set_solver_cap(src, cap)
                open(mf, "w", encoding="utf-8").write(src)
                wall = CLASSIFY_WALL if cap is None else cap + 15
                ok, out = L.lake_build(L.target_of(mf), wall=wall)
            v = classify_target(ok, out)
            if v == "closes":
                rec = {"status": "valid", "tactic": tac, "level": level, "import": imp, "verdict": "closes"}
                break
            last_out, rec["verdict"] = (out or ""), v
            if v == "sat":       # false premise (only euclid_finish yields SAT) — a MAP BUG; stop probing
                break
        results[name] = rec
        if rec["status"] != "valid":
            outputs[name] = "\n".join(last_out.rstrip().splitlines()[-12:])
    return results, outputs


def write_tags(propdir, results, original_src):
    """Merge this prop's per-assumption tags into scripts/assumption_tags.json (keeping other props).
    Record {tag: valid|gap, closed_by: <tactic>|null, level: <rung>|null, verdict: <raw>, text, type} per
    have. `tag` is what the enforcers read (unchanged: valid/gap); `closed_by`/`level` are the graded
    triviality measure (post-processable — level 1=rfl … 5=euclid_finish; null on gap)."""
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
            rec = results.get(hn) or {"status": "gap", "tactic": None, "level": None, "verdict": "error"}
            entry[hn] = {"tag": "valid" if rec["status"] == "valid" else "gap",
                         "closed_by": rec.get("tactic"), "level": rec.get("level"),
                         "verdict": rec.get("verdict", "error"),
                         "text": text, "type": L._norm(typ)}
    data[rel] = entry
    tmp = TAGS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")
    os.replace(tmp, TAGS_FILE)


def report(propdir, results, outputs, original_src, dry_run):
    rel = os.path.relpath(propdir, L.BOOK_ROOT)
    rows = []
    for name, _bs, _indent, assumptions in sentence_blocks(original_src):
        for i, (text, _typ, _override) in enumerate(assumptions, 1):
            hn = have_name(name, i)
            rows.append((hn, results.get(hn) or {"status": "gap", "verdict": "error"}, text))
    n = len(rows)
    valid = [(hn, rec, t) for hn, rec, t in rows if rec.get("status") == "valid"]
    gaps = [(hn, rec, t) for hn, rec, t in rows if rec.get("status") != "valid"]
    mode = "DRY-RUN (no writes)" if dry_run else "PERSISTED"
    print(f"[assumptions] {rel} — {mode}")
    print(f"  {n} assumption(s): {len(valid)} valid (closed), {len(gaps)} gap(s).")
    if valid:
        print("  VALID (cheapest ladder rung that closed it — higher level = less trivial):")
        for hn, rec, text in valid:
            print(f"    - {hn}  [L{rec.get('level')} {rec.get('tactic')}]: {text}")
    if gaps:
        print("  GAPS (no ladder rung closed it — Phase B must prove):")
        for hn, rec, text in gaps:
            v = rec.get("verdict")
            flag = {"sat": " [SAT — premise FALSE, likely a MAP BUG]",
                    "crash": " [euclid_finish CRASHED — tooling limit on this goal shape; Phase B proves "
                             "it directly, not a deep Euclid gap]",
                    "error": " [Lean error — check the type / map]",
                    "hard": " [euclid_finish could not close at 30s]",
                    "wall": " [inconclusive at cap]"}.get(v, "")
            print(f"    - {hn} ({v}){flag}: {text}")
            if dry_run and outputs.get(hn):
                for ln in outputs[hn].splitlines():
                    print(f"        | {ln}")


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
    """STEP B — classify the already-materialized haves (ladder), then persist IN PLACE + tag (or revert if
    dry_run). Requires an intact frame (STEP A build passed, or the human fixed it).

    After persisting, a FINAL build of the COMBINED Main is run: each ladder probe verified ONE have with
    the others still in their pre-classify bodies, so the all-winners-at-once state is otherwise unverified.
    If that build fails, STOP loudly — tags are NOT written (baseline stays uncorrupted) and the persisted
    Main is left for review (a human/`/faithful-assumptions` fix), exactly like STEP A's fail-closed."""
    rel = os.path.relpath(propdir, L.BOOK_ROOT)
    mf = L.main_file(propdir)
    verdicts, outputs = classify_all(propdir, book)
    disk = open(mf, encoding="utf-8").read()                 # materialized haves (+ any manual frame fix)
    if dry_run:
        open(mf, "w", encoding="utf-8").write(original)      # revert — pure diagnostic
        report(propdir, verdicts, outputs, disk, dry_run)
        return 0
    open(mf, "w", encoding="utf-8").write(apply_verdicts(disk, verdicts))
    ok, out = L.lake_build(L.target_of(mf), wall=L.main_wall(propdir))
    if not ok:
        print(f"[assumptions] {rel} — ⚠ STOP: the PERSISTED Main did NOT compile after classification "
              f"(the combined winning-tactic bodies + imports). Tags NOT written; the persisted Main is "
              f"LEFT IN PLACE for review. Fix it, then re-run with `--tag-only`.")
        for ln in "\n".join((out or "").rstrip().splitlines()[-12:]).splitlines():
            print(f"    | {ln}")
        return 1
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

    present = {m.group(2) for m in _HAVE_HEAD_RE.finditer(original)}

    # --tag-only: STEP B ONLY on the EXISTING have set (the repair path) — re-classify in place, never
    # (re-)materialize, never delete, never prompt.
    if tag_only:
        if not present:
            print(f"ERROR: --tag-only but no `stepK_assumptionN` haves in {rel}. Run `assumptions.py "
                  f"{rel}` (no flag) first — a bare run materializes + build-checks.")
            return 2
        try:
            return _step_b(propdir, book, original, dry_run=False)
        except BaseException:
            open(mf, "w", encoding="utf-8").write(original)
            raise

    # --dry-run over an ALREADY-materialized prop stays a pure diagnostic (re-classify in place + revert);
    # it never does the destructive re-materialize below.
    if dry_run and present:
        try:
            return _step_b(propdir, book, original, dry_run=True)
        except BaseException:
            open(mf, "w", encoding="utf-8").write(original)
            raise

    # BARE run = ALWAYS materialize from the CURRENT `-- @assumption` comments (the source of truth). If
    # haves already exist, RE-MATERIALIZE FROM SCRATCH: delete them all + re-add from the current comments,
    # so an added / removed / retyped assumption is reflected (the old auto-skip silently ignored added
    # ones). Confirm first — a re-run is interactive (a fresh sweep has no haves ⟹ never prompts), so no
    # --yes flag is needed; a non-TTY/EOF answer is "no" (abort, no destructive write). Reverts below still
    # target `original` (the TRUE on-disk content), so a crash restores the prior state, not the stripped one.
    to_materialize = original
    if present:
        print(f"[assumptions] {rel} — {len(present)} assumption have(s) already materialized. A bare run "
              f"RE-MATERIALIZES FROM SCRATCH: DELETE all {len(present)} and re-add from the current "
              f"`-- @assumption` comments (reflecting any added / removed / retyped assumption).")
        if not _confirm("  Proceed? [y/N] "):
            print(f"[assumptions] {rel} — aborted; no changes. (Use `--tag-only` to only RE-CLASSIFY the "
                  f"existing haves without re-materializing.)")
            return 0
        to_materialize = strip_materialized(original)

    # STEP A — materialize the all-sorry haves (from the current comments), then build-check Main.
    open(mf, "w", encoding="utf-8").write(materialize(to_materialize))
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
    ap = argparse.ArgumentParser(
        description="The Assumption Phase: materialize a `have` per @assumption, then classify each by a "
                    "ladder (1 rfl, 2 assumption, 3 linarith, 4 nlinarith, 5 euclid_finish@30s); persist "
                    "the first tactic that closes it (tag @assumption_valid + record level/closed_by) or "
                    "@assumption_gap if none. Re-builds the combined Main and STOPS if it fails.")
    ap.add_argument("propdir", help="Proposition directory, e.g. Book1/Prop01")
    ap.add_argument("--dry-run", action="store_true",
                    help="Classify + REPORT only; revert every edit, write nothing (pure diagnostic).")
    ap.add_argument("--tag-only", action="store_true",
                    help="STEP B ONLY: re-run the ladder + re-tag already-materialized haves, skipping "
                         "STEP A (materialize). Use after a manual frame fix (wlog/Hsym) or to re-classify "
                         "with an updated ladder. Errors if no haves are materialized. NOTE: a plain run on "
                         "an already-materialized prop does this automatically (never re-materializes).")
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
