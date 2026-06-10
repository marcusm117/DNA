---
name: faithful-prove
description: >
  PHASE B of making a Euclid proof faithful (LeanEuclidPlus, Book 2): prove each Euclid sentence's
  step, IN ISOLATION, using the recursive SF/SP/P atom and the `check_step.py` script. Main's sentence
  bodies stay `:= by sorry` the whole time; the SCRIPT does all wiring/trace_state transiently — you
  only ever write proof bodies and add `have`+backing-file decompositions. Use AFTER the sentence map
  is written and human-approved (`faithful-map` / Phase A). When `check_step.py <propdir> --all` exits
  0, STOP — Phase C (the human running `wire_main.py`) is mechanical, not a skill. Delegates the actual
  proving to `prove-euclid`. Invoked with a path, e.g. `/faithful-prove Book2/Prop04/Main.lean`.
---

# Phase B — prove each step with the recursive SF/SP/P atom (the scripts own all wiring)

By now (via `faithful-map` / Phase A, human-approved) `Book<N>/PropNN/Main.lean` is the proposition
signature + `euclid_intros` + the object-producing constructions + one
`euclid_sentence "loc" "txt" (stepN : <claim>) := by sorry` per Euclid sentence + the intro/conclude
bookends + the trailing `exact`/`rw` chain. **Every logical body is `:= by sorry`. There are no step
files yet.** Your job: create and prove each step's backing file, recursively decomposing until every
build is ≤30s — WITHOUT ever wiring Main or building an all-wired container yourself. A script does
all of that.

> **READ `prove-euclid` FIRST — hard prerequisite.** All actual proving (decompose → sorry-skeleton →
> fill, the pattern gallery, the 30s rule, explicit `euclid_apply` chains) is `prove-euclid`'s job.
> This skill is the faithfulness wrapper: it tells you the FILE STRUCTURE and the SCRIPT-DRIVEN
> verification loop around that proving.

---

## THE MENTAL MODEL — ONE recursive atom, four nouns (internalize this; nothing else)

- **Container** = any `.lean` file with a tactic proof: `Main.lean`, any `stepN.lean`, a sub-file, …
  recursively. A container may mix REAL `euclid_apply` proof work (must build ≤30s) AND
  `have … := by sorry` sub-nodes.
  > **CONVENTION — `Main` is NOT a node** (it's the root container; it has no backing file, no claim,
  > no parent). So you NEVER pass `Main` as a node argument. The ONLY no-node command is
  > `check_step <propdir> --provable` = "build Main, tolerate sorry" (the Phase-A skeleton check; Main
  > having no parent gets only the build, not SF/SP). `--sufficient`/`--suppliable` with no node, or
  > with `Main`, FAIL with a message saying exactly this. To check a SENTENCE inside Main, pass that
  > sentence's node (`step5`), whose container is Main.
- **Goal node** = a named `:= by sorry` body. Two forms, identical at the proof level:
  - **Main only:** `euclid_sentence "loc" "txt" (stepN : C) := by sorry`  (from Phase A — don't add these).
  - **anywhere:** `have <name> : C := by sorry`  (you add these when decomposing).
- **Backing file** = the helper that proves a node. **NAMING LAW (the script enforces it, abort-loud):**
  > node name  ≡  `<name>.lean` basename  ≡  `theorem helper_<book>_<name>`.
  > `have step27_bigsq : … := by sorry` ↔ `step27_bigsq.lean` ↔ `theorem helper_2_step27_bigsq`.
  Node names are globally unique within a prop.
- **Wiring** = a node's `sorry` replaced by `euclid_apply (helper_<book>_<name> <objs>); euclid_finish`
  **PLUS the `import Book<N>.PropNN.<name>` that makes that helper resolve** — wiring is BOTH halves.
  **ONLY the scripts ever write wiring (body + helper import) or `trace_state`. You NEVER type any of
  them into a file.** You write proof bodies and add `have`+backing-files; the script wires + imports
  transiently and always reverts.

### THE IMPORT INVARIANT (the LLM never imports a helper/step file)
A dev-state container imports ONLY `SystemE` + the **cited-proposition** imports its own proof uses
(e.g. `import Book.Prop29` for an `euclid_apply (proposition_29'''' …)` you wrote) — those are proof
content you DO write. It imports NONE of its pipeline backing/step files; the script adds an
`import Book<N>.PropNN.<name>` only while it transiently wires that node, and removes it on revert.
This is what makes per-node checks fast and isolated (checking node N pulls in only N's backing olean,
not every sibling). `check_step … --check` flags any stray `Book<N>.PropNN.*` import as an error.
**Reach a sub-lemma ONLY as a `have`-node** (`have <sub> : <concl> := by sorry`; the script wires +
imports it) — NEVER hand-write a helper `euclid_apply` or a helper import.

### THE PRIME DIRECTIVE (the one invariant you must never break)
> **At every stage, every `.lean` file in the prop folder builds with its current sorries. If any file
> ever fails to build, STOP and fix that before doing anything else.**

---

## THE RECIPE — `PROVE(container)` — apply it to each Main sentence, recursing as needed

For each Main sentence `stepN` (one at a time; order is free, parallel agents fine), and recursively
for every backing file you create:

```
Can I close this goal directly (real euclid_apply chain, no new node) and build it ≤30s?
  YES → write that proof; verify it green with `check_step Book<N>/PropNN --provable <thisnode>` → DONE.
  NO  → introduce a sub-fact F. NEVER guess its signature:

  (a) SEE THE CONTEXT (script-owned trace_state; addressed BY NODE NAME):
        python3 scripts/check_step.py Book<N>/PropNN --context <node>
      Prints the REAL hypotheses available at that node. For a brand-new fact F, first stub
      `have F : <claim> := by sorry` and use it to close the goal, then --context F.
      ⚠ AID, NOT AUTHORITY: euclid_finish can also discharge facts NOT listed (between/sameSide/
      distinctness via SMT). The authoritative test is SP below, not this list — don't over-split.

  (b) RUN SF — Sufficient (cheapest, FIRST, before any backing file exists):
      with `have F : <claim> := by sorry` in place and USED to close the parent,
        python3 scripts/check_step.py Book<N>/PropNN --sufficient F
      builds the CONTAINER (claim as sorry, no wiring). Green ⟹ the claim is well-typed AND F suffices
      to close the goal. Fails ⟹ F is bogus → fix the CLAIM; do not start proving it.

  (c) CREATE the backing file F.lean (naming law):
        import SystemE   (+ the specific Book.PropMM / Book2.PropMM.Main it CITES — proposition
                          citations only; NEVER import another helper/step file)
        set_option systemE.solverTime 30 in
        theorem helper_<book>_F <objects from (a)> <hyps from (a)> : <claim> := by sorry
      Hyps may ONLY be names available at the call site (prop hyps/objects + constructions above the
      sentence + earlier nodes' claims). If a proof needs something else, that something becomes
      ANOTHER `have`+backing-file (recurse) OR is derived in-body — never an unsuppliable hypothesis.

  (d) RUN SP — Suppliable (BEFORE proving; order matters):
        python3 scripts/check_step.py Book<N>/PropNN --suppliable F
      The script wires ONLY F in its container, builds, reverts. PASS ⟹ F's hyps are suppliable.
      FAIL ⟹ it names the failing euclid_apply → fix F's objects/hyps; re-run. (A FAIL can show as a
      30s-wall kill when an impossible hyp makes SMT thrash — same remedy: fix the signature.)

  (e) RUN P — Provable: PROVE(F.lean) — RECURSE, same recipe one level down, until F builds ≤30s.
      `check_step.py Book<N>/PropNN --provable F` builds F.lean and reports zero-sorry (done) or the
      file:lines where sorries remain.
```
> **In practice, just run `python3 scripts/check_step.py Book<N>/PropNN <node>` (no flag).** It runs
> SF → SP → P in that order and stops at the first failure — telling you exactly what to fix next. The
> individual `--sufficient`/`--suppliable`/`--provable` flags are occasional diagnostics; the bare
> command is the everyday driver.
> **ALL builds go through `check_step` — the agent is HARD-DENIED raw `lake build` / `safe_build.sh`.**

- **30s is recursive and absolute.** Every file carries `set_option systemE.solverTime 30 in`; every
  `check_step` build is also killed at 30s wall. Exceed EITHER ⟹ the node is too big → **decompose
  into more backing files; NEVER raise a cap.** "Simplify until 30s works" is the whole loop.
- **Shared logic → ONE generic backing file**, reused by many nodes (e.g. a `rect_area` helper). Never
  copy-paste a proof across files.
- **You never wire Main, never build an all-wired container, never run `--all` except at the very end.**

---

## SYSTEM-E QUICK REFERENCE (the area-heavy surface you actually prove with)
Grep `SystemE/Theory/Inferences/{Metric,Transfer,Diagrammatic}.lean` + `Relations.lean` for exact
signatures; the high-value ones:
- **Convention:** "rectangle contained by X,Y" = `|X|*|Y|`; "square on X" = `|X|*|X|`; no square axiom
  (it's the right-angled case of `rectangle_area`). Figure areas = sums of `Triangle.area △ p:q:r`;
  `Triangle.area` is permutation-invariant (`area_symm_1/2`, Metric.lean) — order is cosmetic.
- `rectangle_area a b c d AB CD AC BD : formParallelogram … ∧ ∠a:c:d = ∟ →`
  `(area△a:c:d + area△a:b:d = |a─b|*|a─c|) ∧ (area△b:a:c + area△b:d:c = |a─b|*|a─c|)`.
- `parallelogram_area …` (diagonal triangle-area identity); `sum_parallelograms_area a b c d e f … :`
  `formParallelogram … ∧ between a e b ∧ between c f d →` 4 sub-triangles sum to 2 halves (split/glue
  rectangles). `sum_areas_*`, `degenerated_area_*` (Transfer); `area_gte_zero` (Metric).
- Constructions (objects, already applied in Main): `proposition_46`/`46'` (square on a line, 5-tuple),
  `proposition_31` (parallel), `intersection_lines`, `line_from_points`.
- **Cross-book citations: fully-qualify** — `Elements.Book1.proposition_M` (Book-2 names collide with
  Book-1's short names). `import Book.PropM` (Book 1, flat) / `import Book2.PropM.Main` (Book 2).

## HOW THE DEPENDENCY CHECK WORKS (why citations resolve through the wiring)
A sentence's `[Prop.~B.M]` citation is satisfied iff some `proposition_*` in the **transitive
dependency closure** of a constant `euclid_apply`'d in that sentence's block resolves to Book B's prop
M — at any depth, by compiler identity. The script wires each sentence as `euclid_apply (helper_<book>_
stepN …)`, and the olean checker follows the closure INTO `stepN.lean` (and its sub-files), so a prop
cited inside your backing file counts. The one rule inside backing files: cite a prop via
`euclid_apply`, **never** term-mode `:= by exact proposition_M …` (that bypasses recording).

---

## THE FILE STRUCTURE (where backing/sub files go)
- One Euclid sentence = one `Book<N>/PropNN/stepN.lean` (theorem `helper_<book>_stepN`). NEVER inline a
  sentence's proof into Main, never merge two sentences — each must build in isolation.
- A hard step decomposes into more files (never fewer):
  - a few subs → flat in the prop folder: `Book<N>/PropNN/stepN_<sub>.lean` (module
    `Book<N>.PropNN.stepN_<sub>`, theorem `helper_<book>_stepN_<sub>`), referenced as a `have stepN_<sub>`
    node inside `stepN.lean` — the script wires + imports it. NEVER a hand-written
    `euclid_apply (helper_…)` + manual import; every helper call is a node.
  - a MASSIVE step with many subs → its own subfolder `Book<N>/PropNN/stepN/<sub>.lean` (module
    `Book<N>.PropNN.stepN.<sub>`), with the step lemma at `Book<N>/PropNN/stepN/Main.lean`. Lake's
    prefix rule builds these with no lakefile change.
- Everything stays in the prop's folder tree. NO `Scratch/`, no merge step. The `check_step.py`
  scripts discover every file automatically.

---

## THE LOOP IN PRACTICE (per prop)
1. (optional, anytime) `python3 scripts/check_step.py Book<N>/PropNN --check` — instant, no-build
   integrity scan: naming law, every node has a backing file, every file capped at 30s, nothing
   pre-wired. Run it whenever you want a fast "is my tree structurally sound" answer.
2. For each sentence, run the SF/SP/P recipe above (decomposing recursively), verifying every node with
   `python3 scripts/check_step.py Book<N>/PropNN <node>` (or `<N>` for `stepN`) — the no-flag command
   runs SF→SP→P and tells you what to fix next. ALL builds go through `check_step` (raw `lake`/
   `safe_build` are hard-denied). ONE node at a time.
3. SF/SP run BEFORE you prove a body (the no-flag command does them first), so you never sink effort
   into a claim that doesn't close the goal or a signature the parent can't supply.
4. **MANDATORY LAST ACTION:** `python3 scripts/check_step.py Book<N>/PropNN --all`. It re-runs SP + P
   over every node bottom-up (sub-nodes before parents) and STOPS at the first/deepest failure. Exit 0
   ⟹ the Phase-C wired build is GUARANTEED green AND sorry-free. This is the ONLY time you run `--all`.
5. Delete any `-- dev:` notes from your backing files (comment cleanup belongs to end of Phase B).
   Then STOP — hand off to the human for gate B + Phase C. Do NOT run `wire_main.py` yourself.

---

## EXIT PHASE B — what "done" means
Done ⟺ `check_step.py Book<N>/PropNN --all` exits 0 (and `--check` is clean). That output literally
proves: every node is suppliable (S) AND every backing file builds with ZERO sorry in its
final-assembly state (P — a leaf as-is, a container with all its sub-nodes wired, so a stray `sorry`
anywhere is caught here, not deferred) ⟹ **the human's `wire_main.py` build cannot fail and is
sorry-free.** STOP there. Phase C is mechanical (the human runs `wire_main.py` + `check_faithful.sh` +
the guards); it is NOT a skill and you do not perform it.

## INTEGRITY
- NEVER fake it (prove-euclid rules): no `sorry`/`admit`/`native_decide`/`axiom` in a finished backing
  file; "it builds" with a sorry warning ≠ proved (`check_step` catches it — a leaf with sorry FAILS P).
- NEVER hand-write wiring or `trace_state` into any file — the scripts own those (and revert them). If
  you ever see a stray `euclid_apply (helper…)` or `trace_state` left in a file, a script was
  interrupted; re-run it or restore the file.
- Don't change a `step_n` CLAIM TYPE (guarded by `check_steps.py`) or a `proposition_*` statement
  (guarded by `check_signatures.py`). If a claim itself is wrong/unprovable, STOP — it's a Phase-A
  error; tell the human.