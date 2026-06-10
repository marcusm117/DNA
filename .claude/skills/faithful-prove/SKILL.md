---
name: faithful-prove
description: >
  PHASE B (+ final gate) of making a Euclid proof faithful (LeanEuclidPlus, Book 2): prove each
  sentence's step lemma in `Book<N>/PropNN/stepN.lean`, then verify the whole prop is faithful. Use
  AFTER the sentence map is written and human-approved (the `faithful-map` skill / Phase A) — i.e.
  when `Book<N>/PropNN/Main.lean` has real `euclid_sentence` claim types and the `stepN.lean` files
  are sorry-stubs. Delegates the actual proving to the `prove-euclid` skill. Invoked with a path,
  e.g. `/faithful-prove Book2/Prop04/Main.lean`.
---

# Phase B + final gate — prove the step files, then verify faithful

By now (via `faithful-map` / Phase A, human-approved) `Book<N>/PropNN/Main.lean` has the full
sentence map: each `euclid_sentence` has a real claim type and is discharged by
`euclid_apply (helper_<book>_stepN …); euclid_finish`, and each `Book<N>/PropNN/stepN.lean` holds a
`sorry`-stub `theorem helper_<book>_stepN`. Your job: **fill those proofs**, then run the
authoritative faithfulness check. Nothing to "reunite" — Main already calls the steps.

> **READ `prove-euclid` FIRST — hard prerequisite.** All actual proving (decompose → sorry-skeleton →
> fill, the pattern gallery, the 30s cap, explicit `euclid_apply` chains) is `prove-euclid`'s job.
> This skill is just the faithfulness wrapper around it.

> **The claim types are FROZEN.** Phase A's approved `step_n` types are ground truth — you prove them
> as written, you do NOT change them. If a claim turns out wrong/unprovable, that is a Phase-A error:
> STOP and tell the human (re-do the map), don't silently re-type. `scripts/check_steps.py` will catch
> any change. Likewise NEVER touch a `proposition_*` signature (`scripts/check_signatures.py` guards it).

---

## ENVIRONMENT

- **First Bash call: `cd LeanEuclidPlus`** (session starts at repo root `DNA/`; all paths + permission
  allow-rules are relative to `LeanEuclidPlus/`; cwd persists). Don't chain `cd … && …`.
- Read with Read/Grep, never `cat`/`sed`/`find -exec`, never chain shell commands (CLAUDE.md).
- Build a single step in isolation: `scripts/safe_build.sh Book<N>.PropNN.stepN` (~30s). Build the
  whole prop: `scripts/safe_build.sh Book<N>.PropNN.Main`. Bare, no pipes, no `timeout`.
- Each prop is a folder `Book<N>/PropNN/`: `Main.lean` + `stepN.lean` (+ `stepN_<sub>.lean` for
  sub-decompositions). Everything stays in the folder — NO `Scratch/`, NO merge step.

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

## HOW THE DEPENDENCY CHECK WORKS (why you cite via euclid_apply)
A sentence's `[Prop.~B.M]` citation is satisfied iff some `proposition_*` in the **transitive
dependency closure** of a constant applied (via `euclid_apply`) in that sentence's block resolves to
Book B's prop M — by compiler identity, at any depth. So a prop cited *inside* your applied
`helper_<book>_stepN` (i.e. used in `stepN.lean`) counts — the olean checker follows the closure into
the step file. The one rule: a citation is recorded only when the prop/helper enters via
`euclid_apply`. **NEVER discharge a cited step with term-mode `:= by exact proposition_M …`** — that
bypasses recording. (Main was already wired this way in Phase A; just keep it.)

---

## PHASE B — prove each stepN.lean (one file at a time, via prove-euclid)

For each `Book<N>/PropNN/stepN.lean` (a sorry-stub from Phase A):
```
1. The theorem header is fixed: helper_<book>_stepN (objects)(setup hyps)(earlier-step conclusions)
   (cited-prop conclusions) : <the frozen claim type>. Add only the imports it cites
   (import SystemE + the specific Book.PropMM / Book2.PropMM.Main). Keep `set_option systemE.solverTime 30 in`.

2. PROVE via prove-euclid: explicit euclid_apply chains, the pattern gallery, the 30s rule. If a step
   is too big or not entailed: SORRY-FIRST — stub helper_<book>_stepN_<sub> lemmas (own
   stepN_<sub>.lean files) with := by sorry, confirm the parent SKELETON elaborates assuming them,
   THEN prove each sub in its own file. Recurse as needed.

3. (Optional) skeleton-discharge sanity: with stepN still sorry, build Main and confirm the sentence's
   euclid_finish (and the downstream chain) closes ASSUMING the step. If not, the step's TYPE is wrong
   — that's a Phase-A error: STOP and tell the human (do not re-type a frozen claim).

4. GATE B — the step file builds with ZERO sorry:  scripts/safe_build.sh Book<N>.PropNN.stepN
   "Build completed successfully" WITH a sorry warning is NOT done (prove-euclid NEVER FAKE IT).
```
Step files are independent — prove in any order / in parallel; each owns its own file.

---

## FINAL GATE — verify + clean up (NOT a phase; nothing to reunite)

```
1. QUICK: python3 scripts/check_faithful.py "Book<N>/PropNN/Main.lean"
   Fast sanity (text + best-effort deps). ALSO lints Main's body for forbidden bulk goal-closers
   (linarith/nlinarith/ring/simp/omega/…): Main must close its goal ONLY through the
   euclid_sentence/euclid_apply chain — any such tactic in Main fails (step files are exempt; scoped
   algebra is allowed there).

2. AUTHORITATIVE:
     scripts/safe_build.sh Book<N>.PropNN.Main   # whole prop builds, ZERO sorry / errors
     scripts/check_faithful.sh Book<N>           # text + deps book-aware MUST PASS (follows into step files)

3. CLEANUP: delete all dev scaffolding — `-- dev:` notes, per-step TODOs, stale `set_option … 30` caps
   no longer load-bearing, any header comment block. Finished files = imports → theorem → proof.

4. Re-confirm the guards are clean (the human also runs these):
     python3 scripts/check_steps.py Book<N>/PropNN/Main.lean   # frozen claims unchanged
     python3 scripts/check_signatures.py                       # no statement altered
```
The prop is faithful only when `check_faithful.sh Book<N>` PASSES and the build has zero `sorry`.

## INTEGRITY
- NEVER fake it (prove-euclid rules): no `sorry`/`admit`/`native_decide`/`axiom` in a finished proof;
  "it builds" with a sorry warning ≠ proved.
- Don't change a frozen `step_n` claim or a `proposition_*` statement — both are guarded and both are
  Phase-A / ground-truth territory. If one must change, STOP and ask the human.
- Don't game the dep check: the cited prop should be the one the step's reasoning genuinely uses.
