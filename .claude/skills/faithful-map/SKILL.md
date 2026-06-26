---
name: faithful-map
description: >
  PHASE A of making a Euclid proof faithful (LeanEuclidPlus, Book 2): TRANSLATE each of Euclid's
  sentences into a Lean claim type, in `Book<N>/PropNN/Main.lean`. This is pure translation —
  sentence → claim — NOT proving. Use when asked to "map" / "do the sentence map / Phase A" for a
  prop, or as the first step of "make Book2/PropNN faithful". STOP at the end for human review; the
  proving is the separate `faithful-prove` skill. Invoked with a path, e.g.
  `/faithful-map Book2/Prop04/Main.lean`.
---

# Phase A — translate Euclid's sentences into claim types (THIS IS TRANSLATION, NOT PROVING)

Your only job: turn each of Euclid's sentences into one `euclid_sentence` annotation whose Lean type
says **exactly what that sentence asserts**. You write `Book<N>/PropNN/Main.lean` ONLY: the proposition
signature (untouched) + `euclid_intros` + the object-producing constructions + one `euclid_sentence`
per sentence with a real claim type and a `:= by sorry` body + the intro/conclude bookends + the
trailing `exact`/`rw` chain. You create **NO step files** (those are Phase B). You do **NOT** prove
anything and you do **NOT** wire any `euclid_apply (helper…)`. When done you STOP for human review.

This is genuinely easy — it's translation. The mistakes come from drifting into proving or
over-thinking. The three rules below exist to stop exactly that.

---

## ⛔ THREE HARD RULES — read before anything else

**RULE 0 — THE SENTENCE IS THE CLAIM. THE DIAGRAM ONLY RESOLVES LABELS.**
A `step_n` type is a faithful restatement of WHAT THAT EUCLID SENTENCE SAYS — nothing more, nothing
less. The diagram (`Book<N>/data/diagrams/<N>.png`) is for ONE thing: resolving a label — which point
is `G`, which corners a figure-name like "HF" denotes (Euclid names figures by opposite corners),
vertex order of a named region. You may **NOT** build a coordinate model, read geometric facts off the
picture, "audit" claims against coordinates, or expand one sentence into many facts it didn't state.
"HF is also a square" is ONE assertion about HF (e.g. "X is the square on AB" as a single area equation
`area(X) = |a─b|*|a─b|`) — NOT an invented list of four sides + four right angles from the diagram.
Formalizing the picture instead of the words is a faithfulness violation even when the picture is true.

**RULE 1 — DO NOT READ ANY AXIOM FILE.** You may NOT open or grep `SystemE/Theory/Inferences/**`
(Transfer / Metric / Diagrammatic), and you may NOT go looking for "which axiom proves this." That is
the proving phase's job. A claim type is written from ONLY: the Euclid text, the diagram (labels), the
proposition's own signature, and the VOCABULARY list below. If you feel the urge to open an Inferences
file — STOP; you've left translation and started proving. (Reading a construction prop's signature in
`Book/` or a relation def in `SystemE/Theory/Relations.lean` is fine; axiom/Inferences files are not.)

**RULE 2 — ONE SENTENCE AT A TIME. NEVER one-shot the whole map.** Do the sentences strictly in order,
**one at a time**: write THIS sentence's claim type (+ any construction it introduces) → BUILD
(`check_step --provable`, no node) to confirm it elaborates → DEP-CHECK (`check_faithful.py` — confirms
any CONSTRUCTION it cites has its `… as …` in Main; proof-internal cites defer to Phase B) → only THEN
move to the next sentence. Do NOT write several sentences' claims in one
pass, and do NOT design all claims in one giant think — that one-shot habit is what produces the
dependency and claim mistakes (a forgotten `… as …` construction, a claim referencing an object not yet in
scope) that only surface much later. One sentence, confirmed, then the next.

**RULE 3 — EVERY CLAIM IS NON-VACUOUS AND CONTAINS ONLY WHAT THE SENTENCE ASSERTS.** Two failure modes
this rule kills:
- **No vacuous / trivially-true types.** `True`, or a claim that holds by definition regardless of the
  geometry (`|(c─b)| = |(b─c)|` — distance symmetry; `x = x`) is a faithfulness FAIL even though it
  compiles, because it doesn't capture the sentence. EVERY non-structural sentence asserts something —
  state THAT. In particular an **announcement** like "So I say that (it is) also right-angled" asserts
  the thing announced — write the right angles (`∠…=∟ ∧ …`), NOT `True`. (Only `euclid_intro_sentence`
  and `euclid_conclude_sentence` carry no claim.) If you can't think of a non-vacuous claim, you've
  misread the sentence — re-read it.
- **No construction byproducts.** Facts that a construction `euclid_apply` already deposits in Main's
  context (incidences like `k.onLine BE`, `f.onLine CF`, `g.onLine BD` from `intersection_lines`, or
  `b.onLine BD` from `line_from_points`) do NOT belong in a claim type unless the SENTENCE asserts them.
  They're already in scope for later steps for free; echoing them into `step_n` both bloats the claim
  and states things Euclid didn't. A "let X be drawn / described" sentence asserts the FIGURE's defining
  properties (lengths, parallelism, right angles), not every incidence its construction happens to yield.

If you find yourself reading axioms, planning the whole proof at once, building a coordinate model, or
writing facts the sentence didn't state (vacuous fillers, construction incidences, diagram-read geometry)
— you have left Phase A's lane.

### SENTENCE-SHAPE → CLAIM-TYPE (the common patterns — translate by matching the shape)
- **"Let the square FOO be described on XY" / "let PQ be drawn parallel to …"** → the figure's defining
  facts from the cited construction's signature (the lengths, `∠…=∟`, `¬(L.intersectsLine M)`). NOT the
  intersection incidences the construction also produces.
- **"X is a square"** → either its definition `(sides equal) ∧ (angles right)`, OR — for an "X is the
  square on AB" phrasing — the single area equation `area(figure) = |side|*|side|`. Pick the ONE the
  sentence states; do not also invent the other.
- **"figure F is the rectangle contained by P and Q"** → `area(F) = |(p…)| * |(q…)|`.
- **"So I say that … is <property>" (announcement)** → assert the property itself (e.g. the right angles).
- **"angle ABC = angle DEF"** → `∠ a:b:c = ∠ d:e:f`. **"side XY = side ZW"** → `|(x─y)| = |(z─w)|`.
- **"it is on XY" / "on HG, that is to say XY"** → the square's side equals that segment,
  `|(side)| = |(x─y)|` (a locating sentence; keep it the single side-equality, flag to human if unsure).
- **"the figures … are equal to the whole of BIG"** → linear equation summing the sub-figure areas
  `= area(BIG)`. Use the figure's REAL corners (from the diagram label-resolution) so you don't
  double-count one region or omit another.

---

## ENVIRONMENT (minimal — this skill edits Main.lean ONLY; no step files are created in Phase A)

- **First Bash call: `cd LeanEuclidPlus`** (the session starts at repo root `DNA/`; all paths below
  and the permission allow-rules are relative to `LeanEuclidPlus/`). The cwd persists; then run bare
  commands. Do NOT chain `cd … && …`.
- Read files with the Read tool, search with Grep — never `cat`/`sed`/`find -exec`, never chain shell
  commands (see CLAUDE.md).
- Build (skeleton elaboration only) via `python3 scripts/check_step.py Book<N>/PropNN --provable`
  with NO node argument = "build Main, tolerate sorry" (Main has no parent, so it gets the build/
  provable check, not SF/SP). (Raw `lake`/`safe_build.sh` are hard-denied to the agent; `check_step`
  owns every build.)
- Each prop is a folder: `Book<N>/PropNN/Main.lean` (the proposition) + `Book<N>/PropNN/stepN.lean`
  (one per sentence, created in PHASE B). In Phase A you write Main ONLY — no step files. Book 1
  (`Book/`) is flat and untouched.

## INPUTS for each proposition (keyed by prop number `<N>`)
- `Book<N>/data/texts_proofs/<N>.txt` — the canonical English statement + proof + conclusion. THE
  GROUND TRUTH you slice (verbatim).
- `Book<N>/data/diagrams/<N>.png` — the figure, for LABEL RESOLUTION ONLY (Rule 0).
- The annotation FORMAT (the `euclid_sentence "loc" "text" (step_n : <claim>) := by sorry` shape, the
  intro/conclude bookends, the trailing `exact`/`rw` chain) is described in THIS skill. `Book2/Prop01/
  Main.lean`, `Book2/Prop02/Main.lean`, `Book2/Prop03/Main.lean` are DONE, vetted maps you may open to
  see that FORMAT in a finished file. ⛔ But open them for SHAPE ONLY — NEVER copy a claim TYPE across
  props. A claim is a translation of THIS prop's sentence (Rule 0); Prop02's `area△…=|x|*|x|` fits
  Prop02's sentence, not yours. Reading another prop's claim to "see how a square is stated" is exactly
  the proving-by-pattern-match Rule 0/3 forbid — translate your own sentence from its own words.
- **Proposition SIGNATURES are fair game and HELP — read them freely in Phase A.** To know what a
  construction yields (its output objects + their properties) so your claim types name the right
  objects and your construction `euclid_apply` lines are right, READ the cited prop's signature:
  `Book/PropM.lean` (Book 1) or `Book2/PropM/Main.lean` (Book 2) — e.g. open `Book/Prop46.lean` to see
  `proposition_46` returns `(d e : Point)(DE AD BE : Line)` with its equalities/right-angles. Reading a
  prop's STATEMENT (signature) is encouraged; it's the AXIOM/Inferences files (`SystemE/Theory/
  Inferences/**` — how to PROVE) that are off-limits in Phase A. Signatures = what exists; axioms = how
  to prove. Phase A needs the former, not the latter.

## CLAIM-TYPE VOCABULARY (all you need — do NOT go hunting beyond this)
Claim types are built from what's already in the proposition's own signature plus this vocabulary:
- lengths `|(a─b)|`, products `|(a─b)| * |(c─d)|` ("rectangle contained by", "square on" = `|x|*|x|`)
- angles `∠ a:b:c`, right angle `= ∟`
- areas as sums of `Triangle.area △ p:q:r` (a figure split into triangles; `Triangle.area` is
  permutation-invariant in its 3 vertices, so vertex order is cosmetic)
- incidence/order: `.onLine`, `between a b c`, `¬(L.intersectsLine M)`, `.sameSide`, `.opposingSides`
- relations: `formParallelogram a b c d AB CD AC BD`, `distinctPointsOnLine`, `formTriangle`
That is the whole surface. If a sentence's claim seems to need something outside this, re-read the
sentence — you're probably trying to prove it, not state it.

---

## THE PROCEDURE

### A1 — split the text into sentences (no Lean types yet)

```
1. READ Book<N>/data/texts_proofs/<N>.txt; look at the diagram for label resolution. (The annotation
   FORMAT is described in this skill; the done Prop01/02/03 Mains show it in a finished file — open for
   shape only, NEVER to copy a claim type, see INPUTS above.)

2. WIPE THE OLD PROOF. Main.lean currently has an UNFAITHFUL proof. Delete the entire body after
   `:= by` down to just `euclid_intros`. DO NOT touch the signature (theorem proposition_N : ∀ … :=)
   — leave those lines byte-for-byte; it is checked by scripts/check_signatures.py.
   Ensure `set_option systemE.solverTime 30 in` sits on the line DIRECTLY ABOVE `theorem proposition_N`
   (add it now if the old Main lacked it). Every file in the prop — Main included — carries the 30s dev
   cap; if Main lacks it, the construction `euclid_apply`s run uncapped and `--check` only flags it at
   the very end. (Phase C's `wire_main` strips this back to the 300s default — leave it during dev.)

3. SLICE the text into contiguous locators "<book>.<prop>.0 … k":
     .0     = euclid_intro_sentence  (enunciation + "Let …" + "I say that …")
     1..k-1 = euclid_sentence        (each ATOMIC IDEA — see below)
     last   = euclid_conclude_sentence ("Thus, …" + QED)

   ONE STEP = ONE ATOMIC IDEA, not mechanically one sentence. Euclid often packs several assertions
   into one sentence ("But CB is equal to GK, and CG to KB"); SPLIT such a sentence into one step per
   atomic idea (here: a step for `|CB|=|GK|`, a step for `|CG|=|KB|`). More, smaller steps = more
   systematic and far easier to prove/isolate in Phase B. Use judgement for what's "atomic" (one
   equality, one angle fact, one figure's defining properties).

   TWO HARD CONSTRAINTS on splitting (both mechanical — a bad split FAILS `check_faithful` criterion 1):
   - **Verbatim tiling.** Each step's text is a CONTIGUOUS slice of the original; the slices, joined by
     single spaces in locator order, reproduce the WHOLE file CHAR-FOR-CHAR. Nothing reworded, dropped,
     duplicated, or reordered. So you may split a sentence ONLY at clause boundaries that leave clean
     contiguous slices. If an atomic idea is NOT a clean contiguous span (two facts interleaved in the
     wording), you CANNOT split it — keep it ONE step with a conjunction claim (`… ∧ …`).
   - **Split-only, never merge.** A step covers AT MOST one Euclid sentence. A sentence boundary is
     ALWAYS at least a step boundary — never combine text from two sentences into one step. (If one
     idea spans two sentences, they stay separate steps; the later can use the earlier as a hypothesis.)
   A trailing "For …"/"since …" justification clause STAYS in its idea's step (it's the reason, not a
   new claim).

4. Stub every logical sentence as:  euclid_sentence "<loc>" "<verbatim text>" (step_n : True) := by sorry
   (True = placeholder; structural intro/conclude take no claim/body.)

5. GATE A1 — text + construction deps:  python3 scripts/check_faithful.py "Book<N>/PropNN/Main.lean"
   The text-map line must PASS char-for-char (fix slicing until it does). The dep line is now
   CONSTRUCTION-AWARE: it PASSES when every cited construction prop has its `… as …` in Main, and lists
   proof-internal citations as "deferred to Phase B" (expected — those are satisfied later by a step's
   helper cone; deferred is NOT a failure). Both lines should be green/deferred before gate A.
```

### A2 — fill the real claim types and reasoning annotations, ONE SENTENCE AT A TIME (Rule 2)

Go through the sentences strictly IN ORDER, ONE at a time — fully finishing (steps 1–5 below) for one
`step_n` before touching the next. Do NOT batch several sentences into one pass:
```
1. Replace True with the CLAIM TYPE: what THIS STEP's atomic idea asserts, in the VOCABULARY above.
   Rule 0 — the step's words, not the diagram's geometry. One step → one compact claim for its atomic
   idea (a sentence you split into several steps gives several small claims). Earlier steps' claims are
   available as context.

1.5 [REASONING ANNOTATIONS — INPUTS-ONLY]
   After writing the claim, look at the sentence's TEXT for EXPLICIT reasoning citations: "since X",
   "for X [Prop.N]", "X being equal to Y". For each, decide whether X is:
     (a) an INPUT the step CONSUMES — a prior step's conclusion or a construction property that
         becomes a hypothesis binder — OR
     (b) a fact the step itself PROVES — a conjunct of this step's own claim/conclusion.
   (a) → add a `-- @assumption ("verbatim text substring", lean_type)` line DIRECTLY ABOVE the
         euclid_sentence (possibly with `use_override <proofterm>` if the fact is a conjunct
         projection that `assumption` can't crack, e.g. `use_override step2.1`).
   (b) → do NOT annotate. It belongs in the claim, not in an @assumption.
   **INPUTS-ONLY is the load-bearing rule.** A "since X" that appears in the claim as a proved
   conjunct is NOT an @assumption — it is the claim. Only genuine INPUTS get annotated.

   **When to annotate (examples):**
   - "Since AB equals CE [step2]" — step2's conclusion is an input → @assumption it
   - "for the angle is right [from the construction]" — if the right angle is a hypothesis binder
     coming from an earlier step → @assumption it
   **When NOT to annotate:**
   - "Therefore X is Y" — X is Y IS the claim; no @assumption
   - "So I say that angle FDB is right, for it equals ECB" — if "FDB is right" is a CONJUNCT OF THE
     CLAIM, do NOT annotate it (it is what this step proves, not what it consumes)
   - "Similarly" / "For the same reasons" / vague references → skip (don't fabricate)
   **When in doubt: do NOT annotate.** Better to miss a citation than to annotate a proved conjunct.

   **Format:**
   ```lean
   -- @assumption ("verbatim substring of sentence", lean_type)
   -- @assumption ("another reason", lean_type2, use_override step2.1)
   euclid_sentence "<loc>" "<text>" (stepN : <CLAIM>) := by sorry
   ```
   The text must be a verbatim substring of the sentence (checked by check_faithful.py). The lean_type
   must match the EXACT normalized form of the hypothesis binder it will become (same orientation as
   the binder — e.g. `|(c─e)| = |(a─c)|`, not `|(a─c)| = |(c─e)|`, if that's the binder's form).
   Multiple @assumption lines stack above the sentence; @args may coexist below @assumption lines.

   After annotating, run `python3 scripts/scaffold_step.py Book<N>/PropNN stepN` for this sentence
   → creates `stepN.lean` with those hyp types pre-populated as `(hassump1 : T1) (hassump2 : T2) …`.
   NOTE: scaffold creates the backing FILE but does NOT start Phase B; you still do NOT prove anything
   in Phase A. If a backing file already exists (re-map), scaffold refuses to overwrite — skip it.
   (Sentences with NO explicit reasoning citations: no @assumption, no scaffold in Phase A — their
   backing file is created in Phase B as usual.)

2. The Main sentence body STAYS `:= by sorry` (do NOT wire `euclid_apply (helper …)` into Main in
   Phase A — wiring is temporary in Phase B's per-step script and permanent only in Phase C):
       euclid_sentence "<loc>" "<verbatim text>" (step_n : <CLAIM TYPE>) := by sorry
   Because every body is `sorry`, the Main build here is cheap and SMT-FREE (it only type-checks the
   `have step_n : <claim>`; no helper is discharged). Keeping Main sorry is what lets Phase B revise a
   step's hypotheses freely and cheaply — nothing in Main is committed until C.

3. CONSTRUCTIONS go in Main, BEFORE the sentence that needs the object: object-producing applies like
   euclid_apply (proposition_46 a b AB) as (d,e,DE,AD,BE) / (proposition_31 …) / (intersection_lines …)
   / (line_from_points …). The claim types reference these objects, so they must be in scope. (These
   ARE wired in Main and DO run a tiny precondition SMT — that's fine and expected. Only the step
   discharges (`euclid_apply (helper …)`) are NOT wired yet.)
   CRITERION-3 (construction arm) IS YOUR PHASE-A JOB: every Euclid sentence that cites a CONSTRUCTION
   prop (e.g. "[Prop.~1.46]", "[Prop.~1.31]") must have that `euclid_apply (proposition_N …) as …` present
   in Main (it may sit earlier than the citing sentence — objects are often needed early; the check is
   presence-in-Main, not block-local). A citation to a prop used only INSIDE a step's proof (not a
   construction) is deferred to Phase B (the helper cone will cite it). Confirm with the dep check below.
   IMPORTS: Main imports ONLY `SystemE` + the CONSTRUCTION props it uses (e.g. `import Book.Prop46`,
   `import Book.Prop31`). NEVER `import Book<N>.PropNN.stepK` — step files don't exist yet, and a
   step's import (like its wiring) is added transiently by the Phase-B/C SCRIPTS, never by you.

4. After THIS sentence, BUILD to confirm Main elaborates: python3 scripts/check_step.py Book<N>/PropNN --provable
   (all step bodies are sorry, so NO helper discharge runs — cheap; a non-elaborating claim is a
   vocabulary/missing-object problem — fix it NOW, before the next sentence, while the cause is local).

5. DEP CHECK (construction arm), THIS sentence:  python3 scripts/check_faithful.py "Book<N>/PropNN/Main.lean"
   Instant, no build. Every cited CONSTRUCTION prop must be satisfied by its `… as …` in Main; proof-only
   citations show as "deferred to Phase B" (expected — leave them). Fix any construction citation it
   flags NOW (you forgot the `euclid_apply (proposition_N …) as …`) — number-only, and the human's gate-C
   olean check is book-aware, so don't cite the wrong book's prop number. THEN move to the NEXT sentence
   (back to step 1). Doing 4+5 per sentence — not in one batch at the end — is what keeps every claim and
   construction-citation mistake LOCAL and cheap to fix.
   (`check_step --dependency` is the PHASE-B dep gate — both arms, once helpers exist — not a Phase-A tool.)
```

> **NOTE — step files / signatures are created in PHASE B, not here.** Phase A's deliverable is just
> `Main.lean`: the `euclid_sentence`s with real claim types, `:= by sorry` bodies, and the
> object-producing constructions. The `Book<N>/PropNN/stepN.lean` files (with their candidate
> `theorem helper_<book>_<prop>_stepN <args> : <claim>` signatures) are written and verified in Phase B
> (`faithful-prove`), because choosing a step's hypotheses is part of proving it — and the per-step
> script is what certifies those hypotheses are suppliable. EVERY logical sentence will get its own
> `stepN.lean` (one step = one file, never inlined, never merged) — but that's Phase B's job.

### GATE A — SELF-REVIEW, then STOP for human review
When every claim is a real type and `Main.lean` elaborates (all step files are sorry-stubs), FIRST do
this self-review pass over your own map (these are the exact issues humans keep catching — catch them
yourself):
  □ No `True` and no vacuous/definitional claim (`|ab|=|ba|`, `x=x`) on any non-structural sentence (Rule 3).
  □ Every `@assumption` annotation: (a) text is a verbatim substring of the sentence; (b) the annotated
    type is a genuine INPUT the step consumes — NOT a conjunct of the step's own claim. (If unsure,
    remove the annotation; the INPUTS-ONLY rule is load-bearing.)
  □ No construction-byproduct incidences in any claim type (Rule 3) — only what the sentence asserts.
  □ Every figure-area claim uses the figure's REAL corners; no region double-counted or omitted (Rule 0/3).
  □ No claim expanded into facts the text didn't state (one step → its one atomic idea; split a
    multi-idea sentence into multiple steps rather than cramming, but never invent facts).
  □ Splits tile verbatim (slices reproduce the original char-for-char) and never merge across sentences.
  □ You did not open any `SystemE/Theory/Inferences/**` file (Rule 1).
Fix anything the checklist flags. THEN:
- Report the sentence map: for each locator → its text → its `step_n` claim type, and call out any
  sentence whose faithful claim you were genuinely unsure of (e.g. near-structural "it is on XY"
  locating sentences) so the human can focus there.
- STOP. The human reviews that each claim honestly captures its sentence AND that each @assumption
  annotation is a genuine consumed input (both human-checked — no script fully verifies faithfulness).
  The human then runs `python3 scripts/check_steps.py --save Book<N>/PropNN/Main.lean` to freeze the
  claims AND the @assumption types into `step_signatures.json`. Proving happens next via
  `faithful-prove`. (@assumption types are the source of truth — check_step --all enforces their
  persistence in backing file signatures throughout Phase B.)

**Do not start proving. Do not read axiom files. Do not write a header comment block** (brief
`-- dev:` notes are fine; they get deleted later). If a claim seems impossible to state without
deciding how to prove it, that's a signal you're over-thinking the translation — state what the
sentence says and stop.
