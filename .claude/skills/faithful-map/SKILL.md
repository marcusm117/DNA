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
says **exactly what that sentence asserts**. You write the skeleton of `Book<N>/PropNN/Main.lean` and
sorry-stub `stepN.lean` files. You do **NOT** prove anything. When done you STOP for human review.

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
"HF is also a square" is ONE assertion about HF (like Prop02 `step3` types "AE is the square on AB" as
a single area equation) — NOT an invented list of four sides + four right angles from the diagram.
Formalizing the picture instead of the words is a faithfulness violation even when the picture is true.

**RULE 1 — DO NOT READ ANY AXIOM FILE.** You may NOT open or grep `SystemE/Theory/Inferences/**`
(Transfer / Metric / Diagrammatic), and you may NOT go looking for "which axiom proves this." That is
the proving phase's job. A claim type is written from ONLY: the Euclid text, the diagram (labels), the
proposition's own signature, and the VOCABULARY list below. If you feel the urge to open an Inferences
file — STOP; you've left translation and started proving. (Reading a construction prop's signature in
`Book/` or a relation def in `SystemE/Theory/Relations.lean` is fine; axiom/Inferences files are not.)

**RULE 2 — A FEW SENTENCES AT A TIME, NEVER THE WHOLE FILE IN ONE THINK.** Do NOT design all claim
types in one giant think. Take a small CHUNK (you pick the size — 3–6 related sentences), write their
claim types + any constructions, BUILD to confirm they elaborate, then the next chunk. A long single
think over all sentences is the failure mode.

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
- **"X is a square"** → either its definition `(sides equal) ∧ (angles right)`, OR — matching Prop02
  `step3` "AE is the square on AB" — the single area equation `area(figure) = |side|*|side|`. Pick the
  ONE the sentence states; do not also invent the other.
- **"figure F is the rectangle contained by P and Q"** → `area(F) = |(p…)| * |(q…)|`.
- **"So I say that … is <property>" (announcement)** → assert the property itself (e.g. the right angles).
- **"angle ABC = angle DEF"** → `∠ a:b:c = ∠ d:e:f`. **"side XY = side ZW"** → `|(x─y)| = |(z─w)|`.
- **"it is on XY" / "on HG, that is to say XY"** → the square's side equals that segment,
  `|(side)| = |(x─y)|` (a locating sentence; keep it the single side-equality, flag to human if unsure).
- **"the figures … are equal to the whole of BIG"** → linear equation summing the sub-figure areas
  `= area(BIG)`. Use the figure's REAL corners (from the diagram label-resolution) so you don't
  double-count one region or omit another.

---

## ENVIRONMENT (minimal — this skill only edits Main.lean + creates stub step files)

- **First Bash call: `cd LeanEuclidPlus`** (the session starts at repo root `DNA/`; all paths below
  and the permission allow-rules are relative to `LeanEuclidPlus/`). The cwd persists; then run bare
  commands. Do NOT chain `cd … && …`.
- Read files with the Read tool, search with Grep — never `cat`/`sed`/`find -exec`, never chain shell
  commands (see CLAUDE.md).
- Build (skeleton elaboration only) via `scripts/safe_build.sh Book<N>.PropNN.Main` — bare, no pipes.
- Each prop is a folder: `Book<N>/PropNN/Main.lean` (the proposition) + `Book<N>/PropNN/stepN.lean`
  (one per sentence). You create Main's skeleton + the sorry-stub step files. Book 1 (`Book/`) is flat
  and untouched.

## INPUTS for each proposition (keyed by prop number `<N>`)
- `Book<N>/data/texts_proofs/<N>.txt` — the canonical English statement + proof + conclusion. THE
  GROUND TRUTH you slice (verbatim).
- `Book<N>/data/diagrams/<N>.png` — the figure, for LABEL RESOLUTION ONLY (Rule 0).
- `Book2/Prop01/Main.lean` and `Book2/Prop02/Main.lean` — the FORMAT to imitate (annotation shape +
  how claim types look). Don't read their proofs for strategy; just the shape.
- **Proposition SIGNATURES are fair game and HELP — read them freely in Phase A.** To know what a
  construction yields (its output objects + their properties) so your claim types name the right
  objects and your construction `euclid_apply` lines are right, READ the cited prop's signature:
  `Book/PropM.lean` (Book 1) or `Book2/PropM/Main.lean` (Book 2) — e.g. open `Book/Prop46.lean` to see
  `proposition_46` returns `(d e : Point)(DE AD BE : Line)` with its equalities/right-angles. Reading a
  prop's STATEMENT (signature) is encouraged; it's the AXIOM/Inferences files (`SystemE/Theory/
  Inferences/**` — how to PROVE) that are off-limits in Phase A. Signatures = what exists; axioms = how
  to prove. Phase A needs the former, not the latter.

## CLAIM-TYPE VOCABULARY (all you need — do NOT go hunting beyond this)
Claim types are built from what's already in the proposition's own signature + Prop01/Prop02:
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
1. READ Book<N>/data/texts_proofs/<N>.txt; look at the diagram for label resolution. Skim
   Book2/Prop02/Main.lean for the annotation FORMAT.

2. WIPE THE OLD PROOF. Main.lean currently has an UNFAITHFUL proof. Delete the entire body after
   `:= by` down to just `euclid_intros`. DO NOT touch the signature (theorem proposition_N : ∀ … :=)
   — leave those lines byte-for-byte; it is checked by scripts/check_signatures.py.

3. SLICE the text into contiguous locators "<book>.<prop>.0 … k":
     .0     = euclid_intro_sentence  (enunciation + "Let …" + "I say that …")
     1..k-1 = euclid_sentence        (each one of Euclid's sentences)
     last   = euclid_conclude_sentence ("Thus, …" + QED)
   ONE Euclid sentence (period-delimited) = ONE annotation. Do not split or merge. A trailing
   "For …"/"since …" justification clause STAYS in its sentence (it's the reason, not a new claim).
   Each annotation text is a VERBATIM slice; the slices tile the WHOLE file, joined by single spaces.

4. Stub every logical sentence as:  euclid_sentence "<loc>" "<verbatim text>" (step_n : True) := by sorry
   (True = placeholder; structural intro/conclude take no claim/body.)

5. GATE A1 — text only:  python3 scripts/check_faithful.py "Book<N>/PropNN/Main.lean"
   The text-map line must PASS char-for-char. Fix slicing until it does. (The dep line will fail —
   ignore it, deps belong to the proving phase.)
```

### A2 — fill the real claim types, a FEW AT A TIME (Rule 2)

For each chunk of sentences, for each `step_n`:
```
1. Replace True with the CLAIM TYPE: what the sentence asserts, in the VOCABULARY above. Rule 0 —
   the sentence's words, not the diagram's geometry. Match the Prop02 style (one sentence → one
   compact claim). Earlier steps' claims are available as context.

2. Wire the discharge + stub the step file (so Main elaborates):
     - in Main:  (step_n : <claim>) := by euclid_apply (helper_<book>_stepN <args>); euclid_finish
     - create Book<N>/PropNN/stepN.lean:
         import SystemE   (+ namespace Elements.Book<N> ; open Elements.Book1 only if it cites a Book-1 prop)
         set_option systemE.solverTime 30 in
         theorem helper_<book>_stepN (<args>) : <claim> := by sorry
   (helper_<book>_stepN, file stepN.lean. NEVER name a step theorem proposition_*.)

3. CONSTRUCTIONS go in Main, BEFORE the sentence that needs the object: object-producing applies like
   euclid_apply (proposition_46 a b AB) as (d,e,DE,AD,BE) / (proposition_31 …) / (intersection_lines …)
   / (line_from_points …). The claim types reference these objects, so they must be in scope. (These
   are the ONLY things that "run" in Phase A; their tiny precondition SMT is fine. Step PROOFs are sorry.)

4. After the chunk, BUILD to confirm Main elaborates: scripts/safe_build.sh Book<N>.PropNN.Main
   (sorry runs no heavy SMT; a non-elaborating type is a vocabulary/missing-object problem — fix now.)
   Then next chunk, until no True placeholders remain.
```

### GATE A — SELF-REVIEW, then STOP for human review
When every claim is a real type and `Main.lean` elaborates (all step files are sorry-stubs), FIRST do
this self-review pass over your own map (these are the exact issues humans keep catching — catch them
yourself):
  □ No `True` and no vacuous/definitional claim (`|ab|=|ba|`, `x=x`) on any non-structural sentence (Rule 3).
  □ No construction-byproduct incidences in any claim type (Rule 3) — only what the sentence asserts.
  □ Every figure-area claim uses the figure's REAL corners; no region double-counted or omitted (Rule 0/3).
  □ No claim expanded into facts the sentence didn't state (one sentence → one compact claim).
  □ You did not open any `SystemE/Theory/Inferences/**` file (Rule 1).
Fix anything the checklist flags. THEN:
- Report the sentence map: for each locator → its text → its `step_n` claim type, and call out any
  sentence whose faithful claim you were genuinely unsure of (e.g. near-structural "it is on XY"
  locating sentences) so the human can focus there.
- STOP. The human reviews that each claim honestly captures its sentence (the one thing no script
  checks), then runs `python3 scripts/check_steps.py --save Book<N>/PropNN/Main.lean` to freeze the
  claims. Proving happens next via the `faithful-prove` skill.

**Do not start proving. Do not read axiom files. Do not write a header comment block** (brief
`-- dev:` notes are fine; they get deleted later). If a claim seems impossible to state without
deciding how to prove it, that's a signal you're over-thinking the translation — state what the
sentence says and stop.
