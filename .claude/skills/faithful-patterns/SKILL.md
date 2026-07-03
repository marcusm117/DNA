---
name: faithful-patterns
description: >
  LIVING catalog of recurring Phase-A map-STRUCTURE patterns (reductio / by_contra, superposition /
  "coincide", case-splits, circles, angle-sums …) → an exemplar DONE prop + how to render the sentences
  faithfully. Consulted by `faithful-map` when it hits a structural sentence (reductio / superposition /
  case-split) whose FRAME it must build. Agents APPEND a new entry whenever they resolve a pattern not yet
  here, so future props skip the search. Structure/convention only — NEVER a source of claim types to copy.
---

# Faithful-map structure patterns (the mapper's catalog)

This is the Phase-A analog of `euclid-figures` (which catalogs *proving* recipes). When `faithful-map`
hits a sentence that needs a **structural FRAME** — a reductio, a superposition, a case-split — this
catalog says, per pattern, which **done prop exemplifies it** and **how to render the sentences
faithfully** in `Main.lean`.

## How to use (from `faithful-map`)
1. Match the structural sentence to a pattern below.
2. Open the exemplar prop's `Main.lean` to see the exact frame (structure only).
3. Apply the convention to THIS prop's sentences — **copy the FRAME, never a claim TYPE** (claims are
   this prop's own sentence translations; copying `∠ d:b:c = ∠ a:c:b` from Prop06 is a faithfulness
   violation, copying its `have habsurd : ¬(…) := by intro hne … (step_k : False)` shape is the job).
4. **If you resolve a flag using a convention NOT catalogued here, APPEND a new entry** (Edit this file)
   — pattern name, when it applies, the exemplar prop you used, and the handling. Keep entries terse.

---

## PATTERN: reductio / proof-by-contradiction  ("…is impossible", "…is not…", "similarly, neither…")
**Exemplars:** `Book1/Prop06/Main.lean` (isosceles, first Book-1 reductio), `Book2/Prop14/Main.lean`.
**Tells in split.json:** a construction of the negation ("if AB is unequal…", "let BE be straight-on"),
a contradiction sentence ("The very thing is impossible", "absurd [C.N.5]"), a negation-restatement
("BE is not straight-on"), and often a "similarly / for the same reasons" symmetry sentence.
**Frame (from Prop06):**
- Wrap the reductio body in `have habsurd : ¬(<negation of the goal>) := by intro hne` … and at the end
  the real goal follows (`exact`/`euclid_finish` from `habsurd`).
- The **contradiction sentence** gets claim `(step_k : False)` — proved inside the branch.
- **"X is not …" / "similarly, neither …"** sentences carry NO positive claim: route them to the
  branch tail / the `euclid_conclude_sentence`, not a standalone `euclid_sentence` claim. (They still
  keep their TEXT for tiling — as the conclude sentence or a trailing annotation.)
- A **"one of them is greater"** disjunction → the reductio often nests a `by_cases hgt : <disjunct>`
  with the written case in one branch and the symmetric case via a mirror helper (Prop06's `sym`).
**Forward sentences** (the angle/length equalities before the contradiction) translate normally.

## PATTERN: case-split  ("let AB be the greater", two symmetric cases, "or")
**Exemplar:** `Book1/Prop06/Main.lean` (`by_cases`), plus any Book2 prop using `wlog`.
**Handling:** `by_cases h : <disjunct>` with one branch per case; a symmetric case is handled by a mirror
helper (see Prop06's `sym`) or by repeating the branch structure. Each case's sentences keep their text.

## PATTERN: circle radius from centre  ("since A is the centre, AB = AC")
**Exemplar:** any of Book1 Props 1–3.
**Handling:** the sentence asserts a LENGTH (radius) equality `|(a─b)| = |(a─c)|` — state that, not a
circle predicate. Circle membership sentences ("B lies on the circle") use `b.onCircle α` / `a.isCentre α`.

## PATTERN: superposition / "applied to" / "coincide"  (Props I.4, I.8)
**Exemplar:** `Book1/Prop04/Main.lean` and `Book1/Prop08/Main.lean` (both use the TWO-map form below).
**Frame:** `euclid_apply (superposition …) as (b', c', BC', DC')` births image points AND image lines
(read `Book/Prop0N.lean` + `find.py --name superposition`). Make BOTH maps EXPLICIT so claims name images,
not the opaque primed outputs — `classical` then
`let ptImg : Point → Point := fun p => if p = a then d else if p = b then b' else if p = c then c' else p`
`let lineImg : Line → Line := fun L => if L = AB then DE else if L = AC then DC' else if L = BC then BC' else L`
(the placed vertex↦target is DEFINITIONAL — `ptImg a = d` reduces to `d=d`; the rest are the fresh output
points/lines).
**Rendering — MATCH WHAT COINCIDES (the whole game; getting this wrong is the classic error):**
- POINT coincides with POINT → point-image equality `ptImg c = f`. NEVER the given length.
- LINE / SIDE coincides with LINE → LINE-image equality `lineImg AC = DF`, `lineImg BC = EF`. **NOT** a
  point-endpoint disjunction `(ptImg x=u ∧ …)∨…` — a coincidence of *lines* is about *lines*; the
  endpoint/orientation ("flip") is settled in the PROOF (I.7 / line-uniqueness), never in the claim. A
  line-image equality is orientation-free, so no disjunction is needed.
- SAME typing governs `@assumption`s: "AB coinciding with DE" → `lineImg AB = DE`, not `ptImg a=d ∧ ptImg b=e`.
  (`lineImg BC = EF` follows straight from the superposition — the image lands ON the target line — so it
  doesn't even need the derived endpoint coincidence.) length/angle "equal" → the length/angle equality.
- TRIANGLE / ANGLE coincidence (no map exists) → vertex-conjunction `ptImg a=d ∧ ptImg b=e ∧ ptImg c=f`.
**"two straight-lines will encompass an area" (I.4's Post-1 reductio):** has NO literal rendering — System E
has no area-of-lune object (there is NO triangle here, and a length-product is trivial/wrong). It IS the
configuration `two_points_determine_line` (Post 1) forbids: two distinct lines through the same two points →
`distinctPointsOnLine e f (lineImg BC) ∧ distinctPointsOnLine e f EF`, with `lineImg BC ≠ EF` the reductio
hyp, closing to `False`. REQUIRED reviewer comment: `-- the assertion here cannot be literally expressed in
system E`. "same ends" = constructed & given lines share the base endpoint (`e.onLine EG ∧ e.onLine DE`).
NB `Book/Prop08.lean`'s original proof does NOT use this lines structure (it uses `c'=f` + `by_cases d=g` +
I.7) — faithfulness follows Euclid's SENTENCES ("the sides coincide" = lines), not the original proof.

---

## APPENDING A NEW PATTERN (agents: do this when you hit one not above)
Add a `## PATTERN: <name>` section with: the **tells** (how it shows in split.json / the text), the
**exemplar** done prop you learned it from, and the **handling** (the frame + how each sentence type
renders). Terse. Structure/convention only — never paste a claim type. This is how the next agent
avoids the search you just did.
