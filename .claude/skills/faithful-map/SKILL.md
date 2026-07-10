---
name: faithful-map
description: >
  Phase A of making a Euclid proof faithful (LeanEuclidPlus, Book 1 & 2): turn the sentence split into
  `Book<N>/PropNN/Main.lean`'s claim types, ONE sentence at a time, INTERACTIVELY. Prerequisite:
  `/faithful-split` has produced `split.json` (verified by `check_faithful.py --split`). This skill
  stamps a placeholder `Main.lean` (`(stepN : True)` + `@assumption TODO`, text from split.json so tiling
  is correct by construction) then FILLS each claim, building + checking as it goes, and STOPS for human
  review. It may read anything (diagram, `Book/`, `SystemE`, `find.py`) but PREFERS the vocab/translation
  and only digs deeper when a sentence can't be expressed. This is TRANSLATION, not proving (bodies stay
  `:= by sorry`; proving is `/faithful-prove`). Invoked with a prop path, e.g. `/faithful-map Book1/Prop08`.
---

# Phase A — map Euclid's sentences to claim types, one at a time (TRANSLATION, not proving)

Your job: fill `Book<N>/PropNN/Main.lean` with a Lean claim type per sentence — a faithful restatement of
what THAT sentence asserts. You do this **one sentence at a time**, building and checking as you go, then
**STOP for human review**. You do NOT prove (every body stays `:= by sorry`; proving is Phase B).

**Prerequisite:** `/faithful-split` already ran → `Book<N>/PropNN/split.json` exists and passes
`python3 scripts/check_faithful.py --split Book<N>/PropNN`. If it doesn't, stop and run split first.

## STEP 0 — stamp the placeholder scaffold (deterministic; do this first)
```
python3 scripts/faithful_map_assemble.py Book<N>/PropNN --placeholders
```
This writes `Main.lean` with one `euclid_sentence "<loc>" "<text>" (stepN : True) := by sorry` per
sentence + `-- @assumption ("substring", TODO)` lines (seeded from split's justifications). **The TEXT
is copied from `split.json`, so tiling is already byte-perfect — you must NEVER edit the sentence text,
locators, or ordering.** Your whole job is to replace each `True` with a real claim and each `TODO` with a
real type. (Right after Step 0, `check_faithful` will report every claim as a `True` failure and
`--provable` will report the trailing `exact stepK` mismatch — both are EXPECTED and disappear as you fill.)

**Structural markers from `split.json` are ALREADY STAMPED for you** — you fill, you don't build the frame:
- A **`wts`** entry ("I say that …") comes out as `euclid_wts "<loc>" "<text>"` — no `True` slot, nothing
  to fill.
- A **reductio** (split's `reductio_open` / `contradiction` / `reductio_close` frames) comes out as a
  nested `have habsurd<k> : ¬(sorry) := by / intro hsuppose<k> / … / exact <False-step>` block, already
  indented, with the contradiction step's claim pre-set to `False`. **Fill the `¬(sorry)` with the real
  negated supposition (typically a `≠`, e.g. `¬(|(a─b)| ≠ |(d─e)|)`) and make the trailing
  reductio_close claim match it.** The script does NOT stamp `split_ors`/`by_cases`/`wlog` — if the case
  structure needs one (e.g. I.26's two cases, or a "one of them is greater" symmetric `wlog`), you add it
  around the stamped block. See the STRUCTURAL FRAMES section for the semantics.

## ⛔ THE THREE HARD RULES

**RULE 0 — THE SENTENCE IS THE CLAIM. THE DIAGRAM ONLY RESOLVES LABELS.** A `stepN` type is a faithful
restatement of WHAT THAT SENTENCE SAYS — nothing more, nothing less. The diagram
(`Book<N>/data/diagrams/<N>.png`) is for ONE thing: resolving a label — which point is `G`, which corners
a figure-name denotes, vertex order. Do NOT build a coordinate model, read geometry off the picture, or
expand one sentence into facts it didn't state. Formalizing the picture instead of the words is a
faithfulness violation even when the picture is true.

**RULE 1 — ONE SENTENCE AT A TIME. NEVER one-shot the whole map.** Fill sentences in order, one at a
time: write THIS sentence's claim (+ any construction it introduces) → BUILD / check → then the next.
Batching all claims in one pass is what produces the claim + dependency mistakes that surface late.

**RULE 2 — EVERY CLAIM IS NON-VACUOUS AND CONTAINS ONLY WHAT THE SENTENCE ASSERTS.**
- **No `True` / vacuous claim at the end.** `True`, `x = x`, `|(a─b)| = |(b─a)|` (distance symmetry) are
  all vacuous. Every non-structural sentence asserts something — state THAT. (This guards the CLAIM slot
  `(stepN : …)` ONLY. A trivially-true fact is fine — and often clarifying — inside an `@assumption`
  marker; see the `@assumption` section.)
- **⛔ NEVER RESTATE A GIVEN.** If your claim equals one of the theorem's hypotheses — even mod
  length/angle symmetry (`|(b─a)| = |(e─d)|` when `|(a─b)| = |(d─e)|` is given) — it is VACUOUS: you have
  confused the sentence's JUSTIFICATION for its ASSERTION. The claim is the NEW fact the sentence states;
  the given is an `@assumption`. (This is the #1 real-world failure — e.g. "C coincides with F, on account
  of BC = EF": the claim is *C coincides with F*, and *BC = EF* is the `@assumption`.)
- **No construction byproducts.** Facts a construction already deposits (incidences like `k.onLine BE`)
  don't belong in a claim unless the SENTENCE asserts them.

**RULE 3 — FAITHFULNESS IS THE ONLY PRIORITY; DO NOT OPTIMIZE.** (These are the mistakes that waste hours.)
- **Never collapse a claim** to a logically-equivalent shorter/cleaner/more-provable form. State literally
  what the sentence says, even if redundant or verbose; redundant-but-true conjuncts STAY (one-line note).
  Do NOT simplify for elegance or to make proving easier — that is Phase B's problem, not yours.
- **Assertion vs assumption.** The claim IS the sentence's assertion; a consumed premise is an
  `@assumption`, never a conjunct of the claim, and the assertion is never hidden inside an `@assumption`.
  The `assumption`/`assertion` `spans` in `split.json` already draw this line — follow them.
- **Negation placement (De Morgan).** For "X and Y do NOT / cannot … (respectively)", the `∧` stays
  BETWEEN the parts and each `¬` sits on its OWN part — NEVER wrap a single `¬` around the whole
  conjunction (that silently flips `∧`→`∨` and changes the meaning).
- **Re-derive, don't patch.** Rewrite each claim from the sentence; never leave the comment saying one
  thing and the claim saying another.
- **Comments are ONE line.** If a claim seems to need a bulleted/multi-line comment, that is the signal to
  SPLIT the sentence into atomic ones (re-split) — not to write a long comment.

## ⛔ OUTSIDE-SOURCE BUG → STOP AND TELL THE HUMAN (do NOT silently "fix" it)
A discrepancy you hit while mapping is one of THREE things — only the first is yours to fix outright:
- **OUR bug → fix it, quietly.** The map is unfaithful: an invented order/betweenness, a claim that
  restates a given, a construction that puts a point where Euclid's isn't. Re-derive from the sentence.
- **A Euclid generic-position PROOF gap → fill it + mark `@euclid_gap`.** Euclid reads a true-in-general
  fact off the figure that a degenerate admissible model violates; his theorem still holds. Add the
  implicit case (`by_cases`/`wlog`) and mark the site (CLAUDE.md's `@euclid_gap`). Expected, not a bug.
  **You MUST ship the FRAME, not a TODO.** The `by_cases`/`wlog` split is map-phase STRUCTURAL work (like
  a reductio frame) — build it NOW. Only the degenerate branch's *body* is deferrable to Phase B, and it
  is deferred as a DECLARED node: `have gap_<why> : <the-branch-goal> := by sorry` then `exact gap_<why>`
  (the generic branch keeps Euclid's sentences). **⛔ NEVER leave the false-in-model fact as a bare
  `have hx : e ≠ f := by sorry` with a `-- FIX (pending)` comment.** That `sorry` is UNPROVABLE by design
  (false in the degenerate model), yet NO gate catches it — `check_step --provable` tolerates every sorry
  and the stray-sorry check passes a declared node body — so it silently rots into Phase B as a landmine
  Phase B can never discharge. If you can name a fact as an `@euclid_gap` because it's false in some
  admissible model, you have ALREADY done the reasoning to split on it; splitting is not extra proving,
  it's finishing the map. (Worked: `Book3/Prop14` — `e ≠ f`/`e ≠ g` false when the chord is a diameter →
  nested `by_cases h_ef : e = f` / `h_eg : e = g`, two `gap_*_diam` declared nodes, generic branch derives
  `hef := h_ef`; `Book3/Prop09` is the same shape.)
- **A genuine OUTSIDE-SOURCE bug (NOT ours, NOT a mere implicit case) → STOP + REPORT.** A real error in
  the source: Euclid's own mistake, a translation/text error (the English asserts something inconsistent
  or absent from the Greek), or a wrong editorial citation (a `[Prop.~B.N]` bracket that points at the
  wrong proposition — e.g. III.1 brackets segment-bisection as `[Prop.~1.9]`, but 1.9 is angle-bisection;
  it is I.10). **Do NOT paper over it:** never edit the canonical text, never swap the Lean to chase a
  wrong bracket, never invent a claim/workaround to go green. TELL the human with the evidence and let
  THEM decide — correct the source, accept a documented gap, or (for a wrong citation) add
  `-- @suppress_deps_check "reason"` on its own line directly above the sentence, which waives criterion-3
  for that sentence while the text still tiles byte-for-byte. "Bug" = an outside-source error, never ours.

## READING POLICY (you may read anything — but prefer the translation)
You are NOT restricted: you MAY read the diagram, `SystemE/**`, `Book/PropNN.lean` originals, done Book-2
props, and use `python3 scripts/find.py …`. **But default to the VOCABULARY below + a direct reading of
the sentence.** Only dig deeper (open an axiom, read how `Book/PropM.lean` uses a construction) when a
sentence genuinely can't be expressed from the vocab — e.g. superposition ("applied to" / "coincide",
Props 4/8) is rendered with the `superposition` construction: read `Book/Prop08.lean` (and
`find.py --name superposition`) to see how "C coincides with F" becomes an image-point equality (`c' = f`),
NOT the given `|(b─c)| = |(e─f)|`. Don't over-read: most sentences are a one-line vocab claim.

## STRUCTURAL FRAMES — you EDIT Main's SHAPE, not just fill `True` slots (often NON-trivial)
Filling a claim is usually a one-liner — but some props require you to **RESTRUCTURE `Main.lean`**, and
that is squarely your job, done faithfully. This is NOT always trivial; take it seriously. You edit Main
directly: add the scaffold, move sentences into branches, put the closing in the tail — whatever the
proof's logic requires. Consult **`faithful-patterns`** (the catalog of these shapes + exemplars).

### ⚠ UNDERSTAND EUCLID'S ARGUMENT FIRST — frames are consequences, not keyword triggers

**Before choosing ANY Lean structure** (`by_contra`, `have … := by intro h`, `wlog`, `euclid_wts`, nested
`have` frames), READ THE WHOLE PROOF and understand what Euclid is SEMANTICALLY doing. The Lean structure
is a CONSEQUENCE of that understanding — it is NOT triggered by spotting a phrase.

**The fatal mistake:** pattern-matching individual phrases to tactics. "For if not" is not a mechanical
signal to write `by_contra`. "In fact, X is not Y" is not a mechanical signal for `euclid_wts`. "Neither,
indeed" does not mechanically start a new `have`. You must ask: **what is Euclid's overall argument?
What is he asserting here, and why? What scope does each part span?** The answers to those questions
determine the Lean structure.

**Multiple Lean structures can faithfully encode the same semantic argument.** For a reductio, you might
write `by_contra h` (assumption in scope as a hypothesis, everything inside, closed by `exact h <fact>`)
OR you might write `have habsurd : ¬P := by intro hne; …; exact step_k` (the contradiction closes the
`have`, and Euclid's positive asserting sentences come OUTSIDE the have afterward). Neither is the
"correct" choice in the abstract — the right structure is whichever one faithfully mirrors what Euclid
is doing: where the sentences live in his argument, what scope each hypothesis belongs to, what he
asserts after the sub-argument closes. Only by reading and understanding the argument do you know which
structure to use.

The recurring frame shapes (below) are PATTERNS to recognize — they are not a lookup table. Identify
the argument's shape by reading, then pick the matching structure.

- **Reductio / `by_contra`** — exemplars **`Book1/Prop06`** (isosceles) and **`Book2/Prop14`**
  (quadrature). Wrap the reductio body in `have habsurd : ¬(<negation of the goal>) := by intro hne …`;
  the contradiction sentence's claim is `(step_k : False)`; the closing lives in the tail
  (`exact`/contradiction from `habsurd`). **When the GOAL ITSELF is a negation `¬P`, `euclid_intros`
  already `intro`s it — the goal is `False` and the reductio hypothesis `P` is in context (no `habsurd`
  frame; exemplar `Book1/Prop07`, `Book1/Prop39`). Close the tail with the final positive step applied to
  that hypothesis: `exact step_k ‹P›`.**
  - **⛔ A "…is not…" / "similarly, neither…" sentence is STILL A REAL ASSERTION — give it a real claim,
    do NOT drop it to `euclid_wts`/reroute.** A negation "X is not Y" → the `¬(…)` claim (or, when Y is
    itself "not-parallel/not-unequal", the *un-negated* primitive: "AE is not parallel to BC" →
    `AE.intersectsLine BC`; "AB is not unequal to AC" → `¬(|(a─b)| ≠ |(a─c)|)`). A "similarly / for the
    same reasons / neither is any other …" sentence is a real (often GENERALIZED, e.g.
    `∀ L, a.onLine L → L ≠ AD → L.intersectsLine BC`) assertion that **Euclid simply does not re-prove** —
    it still gets a claim; its body stays `:= by sorry` like every other (deferred to Phase B), which is
    NOT the same as being claimless. Exemplars that DO carry claims: **Prop06 step10** (`¬(…)`),
    **Prop25 step5/step9** (`≠` / `¬<`), **Prop39 step9/step10**. The ONLY genuinely claimless sentences
    are the mid-proof "I say that …" (→ `euclid_wts`) and the leading/trailing bracket sentences
    (→ `euclid_intro_sentence`/`euclid_conclude_sentence`). Reroute-to-claimless is reserved for a
    sentence with NO expressible System-E content at all (e.g. I.4's "two lines encompass an area") —
    it is NOT the default for negations or "similarly".
- **Case-split** — `by_cases h : <disjunct>` / `wlog`, one branch per case; symmetric case via a mirror
  helper or repeated structure (exemplar `Book1/Prop06`).
- **Superposition** — add `euclid_apply (superposition …) as (…)` (it births the image point + phantom
  apex); "coincide" → image equality `c' = f` (exemplar `Book/Prop08.lean`).
- **Mid-text "I say that …"** (the goal announcement, placed AFTER the construction) — map it as
  **`euclid_wts "loc" "text"`** (the what-to-show tactic: STRUCTURAL, no claim, no node, but legal
  mid-proof). Euclid's "I say that X" ANNOUNCES the goal; it is not an assertion that X is already
  proven. X is established by the sentences that FOLLOW it and assembled by the trailing `exact` from
  those real component steps — e.g. `exact ⟨witness, stepFoo, stepBar⟩`, NOT from the WTS sentence.
  ⛔ Do NOT map it as a `euclid_sentence` carrying the goal body: that forces you to *prove X at the
  announcement's position*, but X's supporting facts come LATER in source order, so you'd re-derive the
  whole argument there (or a monolithic helper proves X and the following sentences re-prove it — the
  redundant assert-then-reprove `euclid_wts` exists to kill). `euclid_wts` is symmetric with the already-
  structural closing "Thus X" (`euclid_conclude_sentence`); faithfulness is preserved because X lives in
  the theorem's goal + the real component steps. (⛔ Still NEVER use `euclid_intro_sentence`/
  `euclid_conclude_sentence` mid-proof — those are gated to the LEADING/TRAILING brackets; `euclid_wts`
  is the mid-proof structural tactic.) Exemplars: `Book1/Prop09/10/11/12`.
  **Tail pattern after `euclid_wts`:** the following sentences prove the goal's components under their
  construction labels (e.g. step9 proves `∠ d:a:f = ∠ e:a:f` using auxiliary points D/E, while the goal
  needs `∠ b:a:f = ∠ c:a:f`). If the step types don't match the goal form exactly, add a bridging
  `have hbridge : <goal-type> := by sorry` in the tail (proved in Phase C by euclid_finish from the
  between/on-line facts that D is on AB, E on AC). Similarly, implicit geometric facts not stated by any
  sentence (e.g. `between a d b` in Prop10 — D is the construction intersection) need their own named
  `have`. These are NOT stray sorrys — they are the standard `have <n> : <claim> := by sorry` form.
Open the exemplar's `Main.lean` for the frame SHAPE **(structure only — NEVER copy a claim TYPE; the claim
is THIS prop's own sentence)**. If the proof is a reductio/case-split, the map is a genuine restructuring,
not a fill-in-the-blanks — do it, and do it faithfully.

---

## VOCABULARY (the building blocks — each is a System-E surface form)
There is NO `parallel`/`perpendicular`/`coincidesWith`/`Square`/`Rectangle`/`Parallelogram.area`/
`isRightAngle` predicate — spell each with the primitives below.

### Lengths and products (real-valued: =, ≠, <, >, + all apply)
```
|(a─b)|                    -- length of segment a→b
|(a─b)| * |(c─d)|          -- "the rectangle contained by AB and CD"
|(a─b)| * |(a─b)|          -- "the square on AB"
|(a─b)| = |(c─d)|          -- lengths equal   (also <, >, and sums)
|(a─b)|*|(a─b)| + |(c─d)|*|(c─d)| = |(e─f)|*|(e─f)|   -- sum of squares (Pythagoras, 47/48)
```
### Angles (real-valued: same =, <, >, +)
```
∠ a:b:c                    -- angle at vertex b, rays b→a and b→c
∟                          -- ONE right angle;  ∟ + ∟ = "two right angles";  ∟ / 2 = "half"
∠ a:b:c = ∟                -- "ABC is a right angle" / "at right angles" / "perpendicular"
∠ a:b:c = ∠ d:e:f          -- angles equal;   < / >  for less/greater (exterior angle, 16)
∠ a:b:c + ∠ d:e:f = ∟ + ∟  -- "sum = two right angles"
∠ a:b:c = ∠ d:e:f + ∠ g:h:i -- angle-sum decomposition (exterior = two interior, 32)
```
### Areas (figures as triangle sums — NO polygon/parallelogram area primitive)
```
Triangle.area △ p:q:r
Triangle.area △ a:b:c + Triangle.area △ a:c:d   -- quadrilateral ABCD (opposite corners)
```
### Incidence, order, sides
```
p.onLine L        collinear a b c        between a b c
p.sameSide q L    p.opposingSides q L    ¬(L.intersectsLine M)   -- "AB parallel to CD"
```
### Circles (Book 1)
```
p.onCircle α   p.isCentre α   p.insideCircle α   p.outsideCircle α
-- "since A is the centre, AB = AC" is a LENGTH (radius) equality |(a─b)| = |(a─c)| — state THAT.
```
### Figure-formation relations
```
formTriangle a b c AB BC AC            formParallelogram a b c d AB CD AC BD
formRectilinearAngle a b c AB BC       distinctPointsOnLine a b L
```
### Connectives & comparisons
```
∧      =  ≠  (points/lines & reals)      <  >  ≤  ≥  (reals only: lengths, angles, areas)
```
### Construction calls (for construction sentences — READ the cited prop/axiom signature for arg order)
```
line_from_points a b → AB            intersection_lines L M → p
extend_point L b c → a (between b c a)     extend_point_longer L b c (d─e) → a
point_between_points_shorter_than L b c (d─e) → a     exists_point_between_points_on_line L b c → a
exists_point_opposite L b → a (a.opposingSides b L)
circle_from_points a b → α   intersection_circles α β → p   intersections_circle_line α L → (p,q)
-- cited PROPOSITIONS deposit their signature's outputs (proposition_46 → a square; _31 → a parallel;
--   _11 → a perpendicular; _3 → a cut-off point). For "coincide/applied" superposition, see READING POLICY.
```
For a cited construction (`[Prop.~1.46]`, …) read the prop's signature (`Book/PropM.lean`) for its
argument order + outputs.

### Variable naming
Points lowercase (`a b c … g h`); lines UPPERCASE two-letter (`AB CE GH`). Use the signature's existing
names; new construction points follow the Euclid label (`$E$`→`e`); intermediates `e0`,`e1` then `e`.

### Common sentence-shape → claim-shape
| Euclid says | claim |
|---|---|
| "angle ABC is a right angle" | `∠ a:b:c = ∟` |
| "angle ABC equals angle DEF" | `∠ a:b:c = ∠ d:e:f` |
| "AB is equal to CD" | `\|(a─b)\| = \|(c─d)\|` |
| "the square on AB equals…" | `\|(a─b)\| * \|(a─b)\| = …` |
| "X is the rectangle by A and B" | area (triangle-sum) `= \|(a─…)\| * \|(b─…)\|` |
| "let BG be made equal to A" (construction) | `\|(b─g)\| = \|(a₁─a₂)\|` |
| "let DG be made equal to **either of** AC **or** DF" (construction) | `\|(d─g)\| = \|(a─c)\| ∨ \|(d─g)\| = \|(d─f)\|` — "either…or" is a DISJUNCTION; render it as `∨`, NOT just the first side (I.24.2) |
| "let the equilateral triangle DEF be constructed" (construction) | `formTriangle d e f DE EF DF ∧ \|(f─d)\|=\|(d─e)\| ∧ \|(f─e)\|=\|(d─e)\|` |
| "drawn parallel to AD" (construction) | `e.onLine EF ∧ ¬(EF.intersectsLine AD)` |
| "let EA, EB be joined" (construction) | `distinctPointsOnLine e a EA ∧ distinctPointsOnLine e b EB` |
| "the very thing is impossible" (reductio) | `False` (inside the frame) |
| "BE is not straight-on to CB" (a negation) | `¬ (between c b e)` |
| "Let KHG be added to both" (Common Notion 2, applied to a prior equality `∠HKF=∠GHM`) | the RESULTING sum-equality, a PLAIN assertion: `∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g`. NOT an implication — see the note below the table |
 \|(b─c)\| = \|(b─g)\| → \|(a─l)\| = \|(b─c)\|` |

A trivially-valid claim like this last row is FAITHFUL — not a RULE-2 vacuity violation — precisely
*because Euclid states it as a sentence*. The sentence IS the claim; when Euclid invokes a Common
Notion ("things equal to the same thing…") as its own step, translate it as the implication he asserts,
not as `True`.

**⛔ BUT do NOT reach for an implication when a Common Notion is APPLIED to an already-established
prior fact — assert its CONCLUSION, and consume the prior fact as a prior step / `@assumption`.** The
canonical trap is **"Let KHG be added to both"** (Common Notion 2, applied to a prior equality
`∠HKF=∠GHM`): its faithful claim is the **resulting sum-equality** `∠HKF+∠KHG = ∠GHM+∠KHG` (a plain
assertion). Do NOT render it as `(∠HKF=∠GHM) → (∠HKF+∠KHG = ∠GHM+∠KHG)`. That conditional is an
*arithmetic tautology* — true no matter what the figure looks like — so it carries **none** of the
sentence's geometric content; its only purpose is to dodge the (harmless, RULE-3-permitted) redundancy
with the following "Thus, (sum) = (sum)" sentence. Redundancy is FINE; the tautology-dodge is not. The
prior equality it adds to is a PRIOR SENTENCE already in context (or, if stated *inside* this same
sentence as a "since …" clause, an `@assumption`), never folded into the claim as an antecedent. (The
implication form in the row above is reserved for the *narrow* C.N.1 "equal to the same thing" step where
the premises live inside that very sentence and there is no separately-assertible conclusion; when in
doubt, prefer the plain conclusion + `@assumption`. Same law for "let X be subtracted from both".)

### Figural language stays figural — translate the FIGURE Euclid NAMES, not the consequence it implies
Congruence / base-angle props (I.4–I.8, I.26 …) keep tripping this. The mistake is substituting the
arithmetic that *follows* for what the sentence *says*. Translate what is named:
- **IF THE SENTENCE SAYS "TRIANGLE", THE CLAIM CONTAINS `formTriangle` — full stop** (likewise
  "square"/"parallelogram" → `formParallelogram`). A CONSTRUCTION that NAMES a figure asserts the FIGURE,
  not the construction call's output shape. "let the equilateral triangle DEF be constructed [I.1]" →
  `formTriangle d e f DE EF DF ∧ <the equal sides>`, even though the cited call (`proposition_1'`) only
  *outputs* two length equalities + an `opposingSides` (no `formTriangle`). The call's OUTPUTS are NOT the
  claim; the sentence's word "triangle" is. Build whatever side-lines the figure needs FIRST (silently, as Prop02/Prop10 join the two new sides
  before their triangle sentence: `line_from_points e f as EF`, `line_from_points d f as DF`) so
  `formTriangle` has its lines. Same law for "square"/"parallelogram" → `formParallelogram …`. (This is
  RULE 0: matching a construction's return type instead of the sentence is the single most common figure
  miss — Prop09 step4 was originally written without the triangle for exactly this reason.)
- **"the triangle X = triangle Y"** = *figure/area* equality → `Triangle.area △ x… = Triangle.area △ y…`
  WHEN base and angles are stated as their OWN separate sentences (I.5: base | triangle | angles — the
  "triangle" clause is the one thing base+angles don't cover). ONLY if "triangle = triangle [I.4]" is the
  *bundled* congruence (no separate base/angle sentences — I.6) → the congruence parts
  `|base₁|=|base₂| ∧ ∠…=∠… ∧ ∠…=∠…`. Decider: are base & angles their own sentences? yes → area; no → parts.
- **"the base BC is common to them"** = a shared *side* → `distinctPointsOnLine b c BC`, NOT the vacuous
  distance identity `|(b─c)| = |(c─b)|`.
- **"they encompass a common angle XYZ"** → NAME it: both figures' vertex-angle = `∠ x:y:z`, e.g.
  `(∠ f:a:c = ∠ f:a:g) ∧ (∠ g:a:b = ∠ f:a:g)` — not the re-lettered `∠ f:a:c = ∠ g:a:b`.
- **"they are at / under the base"** (locational) → the claim is the IDENTIFICATION "these ARE the
  [base / under-base] angles", NOT the equality that follows. If the angles already ARE the goal's angles
  (no conversion) it collapses to that equality; if they're auxiliary (need a ray-identity — e.g. F on BD
  ⟹ ∠FBC=∠CBD) the identification is the claim and the goal-conjunct equality is ASSEMBLED in the closing
  tail (`exact ⟨…, h.1.symm.trans (h2.trans h.2)⟩` — a term-mode `exact`, which is not a "bulk tactic").

### Closing the goal — the ONLY two places a `sorry` may appear
A `sorry` is allowed in EXACTLY two slots: a `euclid_sentence "…" "…" (stepN : …) := by sorry` body, or a
`have <n> : <claim> := by sorry`. **A `by sorry` ANYWHERE ELSE is a STRAY sorry and is a hard error** —
most often smuggled into a tail term like `exact ⟨f, by sorry, step6⟩`. (`check_step --provable` now
rejects this at map time; see [[book1-prop09-faithful-map]].)
- **Existential goal `∃ w, P w ∧ Q w`** whose witness has a side-condition NOT asserted by any sentence
  (e.g. `f ≠ a`, `between a h b`): `use <witness>` then discharge each unmet conjunct as its OWN
  `have <n> : <side-cond> := by sorry`, then `exact ⟨…⟩`. NEVER inline the gap as `by sorry` in the
  `exact`. E.g. Prop09 (post-`euclid_wts`): `use f` / `have hfa : f ≠ a := by sorry` /
  `have hangle : ∠ b:a:f = ∠ c:a:f := by sorry` / `exact ⟨hfa, hangle⟩` — `hangle` bridges step9's
  auxiliary-label form `∠ d:a:f = ∠ e:a:f` to the goal form (D on AB, E on AC). Or route side-conditions
  to a Phase-B helper à la Prop11's `between_ahb` (`refine ⟨between_ahb, step23⟩`).
- If a conjunct IS a context hyp, `use <witness>` alone (or a plain `exact ⟨…⟩` over named haves) closes
  it — no sorry needed.

## `@assumption` (INPUTS-ONLY)
Each `-- @assumption ("substring", TODO)` line the scaffold seeded marks a prior fact this sentence
CONSUMES (from split's justifications). Replace `TODO` with the Lean type of that fact — the EXACT
normalized form of the hypothesis binder it becomes (e.g. `|(a─c)| = |(c─e)|`).
**These types are now LOAD-BEARING, not a revisable guess.** After your map is reviewed + saved, the
**Assumption Phase** (`scripts/assumptions.py`, the human runs it) materializes EACH `@assumption` into a
`have stepK_assumptionN`, proves the trivial ones (`euclid_finish`, tagged `@assumption_valid`) and marks
the rest `@assumption_gap` for Phase B — and downstream checks HARD-FAIL if an assumption is dropped or
retyped. So get the type right and don't tag an assertion as an assumption. (`use_override` is retired —
`euclid_finish` splits conjuncts and crosses orientation flips on its own; just write the type.)
**INPUTS-ONLY:** an `@assumption` is a fact the step consumes — NOT a conjunct of the step's own claim. If
a seeded substring is actually the assertion (not a consumed input), delete that `@assumption` line. When
in doubt, drop it.

**⚠ CONSTRUCTION SENTENCES HAVE `@assumption`s TOO — a leading "For since X, let …" clause is a consumed
input.** Don't assume a construction sentence is `@assumption`-free just because the scaffold seeded none
(the split can miss a construction's justification). If the sentence opens "For since X, let Y be
constructed …" / "since X, let …", the "X" clause names a PRIOR FACT the construction consumes — ADD an
`-- @assumption ("X", <type>)` for it (its assertion stays the constructed object's property). Real miss:
I.24.1 "For since angle $BAC$ is greater than angle $EDF$, let (angle) $EDG$ … constructed …" — the
"angle $BAC$ is greater than angle $EDF$" clause (`∠ b:a:c > ∠ e:d:f`, the given) was dropped because the
sentence looked like a pure construction.

**TRIVIALLY-TRUE INPUTS ARE OK HERE (unlike claims).** RULE 2's no-vacuous ban guards the CLAIM slot; an
`@assumption` documents a consumed input, so a definitional / trivially-true conjunct is ALLOWED and is
often the FAITHFUL choice — it makes explicit that a hypothesis really was consumed, so a (paper) reviewer
isn't left wondering where it went. Canonical case: **superposition**. "BC coincides with EF" = (B↦E) ∧
(C↦F); B↦E is definitional (E is the copy's first vertex — the axiom's `d`-slot argument), so it has no
non-trivial equation: write it as `e = e` and pair it, e.g. `@assumption ("$BC$ coinciding with $EF$",
e = e ∧ c' = f)`. Do this CONSISTENTLY everywhere a coincidence/placement is re-invoked (the "if base BC
coincides…" reductio sentence, the "base BC being applied…" restatement), with a one-line note that the
`e = e` conjunct is the definitional half. The CLAIM itself still states a real fact (e.g. `EG = DE ∧
GF = DF`), never `e = e`. (Exemplar: `Book1/Prop08/Main.lean`.)

## PROCEDURE (one sentence at a time)
1. STEP 0 above (stamp the placeholder scaffold). Read `split.json` (roles/justifications) and the diagram
   (labels).
2. For each sentence IN ORDER:
   a. Replace its `(stepN : True)` with the real claim (RULE 0/2, VOCABULARY). For a **construction**
      sentence, ALSO add the object-producing `euclid_apply (…) as …` line(s) in Main BEFORE the sentence
      (the claim references those objects) — and if it calls a cited PROP (`proposition_3`, `_46`, …) add
      `import Book1.PropNN.Main` at the top (foldered Book1, zero-padded, e.g. `import Book1.Prop11.Main`;
      the scaffold stamps only `import SystemE`, so a cited prop is an `unknown identifier` until imported).
      ⛔ The flat `Book/PropNN.lean` tree is DEAD — NEVER `import Book.PropNN`; always the foldered
      `Book1.PropNN.Main` (+ `open Elements.Book1`). And NEVER import `OldBook1`/`OldBook1Variants`.
      For a sentence needing a **frame** (reductio/`by_cases`/`wlog`)
      or a construction beyond the vocab (superposition): add the frame / `euclid_apply (superposition …)`
      — read `Book1/PropNN/Main.lean` for the shape (READING POLICY). Bodies stay `:= by sorry`.
   b. Fill any `@assumption` `TODO` on that sentence (INPUTS-ONLY).
   c. Keep going — do NOT one-shot. When a small batch is filled, BUILD:
      `python3 scripts/check_step.py Book<N>/PropNN --provable` (fix any malformed-claim error it names;
      the trailing `exact stepK` mismatch is expected until the final goal-bearing step is filled).
3. **HARD GATE — you may NOT finish until BOTH commands exit 0. Loop: fix → re-run → repeat.**
   - `python3 scripts/check_step.py Book<N>/PropNN --provable` → **must exit 0** — Main ELABORATES /
     compiles (all-sorry). A malformed claim type fails here on its line; the trailing `exact stepK`
     mismatch persists only until the final goal-bearing step's claim is filled — once all claims are in,
     this MUST be green.
   - `python3 scripts/check_faithful.py Book<N>/PropNN/Main.lean` → **must exit 0** — perfect tiling,
     **ZERO `True`**, construction deps satisfied.
   If either is red, fix the offending claim(s) and re-run. Do NOT proceed to human review with either
   failing — that is the whole point of this stage.
4. Run the GATE-A self-review (below); fix anything, then re-run both checks once more (still both green).
5. **STOP for human review — only once BOTH checks above exit 0.** The human confirms each claim honestly
   captures its sentence, then runs `python3 scripts/check_steps.py --save Book<N>/PropNN/Main.lean`.
   Proving is next (`/faithful-prove`).

## GATE-A SELF-REVIEW (before you stop — the issues humans keep catching)
  □ No `True` and no vacuous/definitional claim on any non-structural sentence; only intro/conclusion
    carry none. Reductio contradiction → `False`; a negation → `¬ …`; add/subtract → the resulting equation.
  □ **No claim RESTATES A GIVEN** (even mod length/angle symmetry) — that's the assertion-vs-justification
    confusion; the given belongs in `@assumption`.
  □ Every `@assumption`: substring is verbatim from the sentence, and the type is a genuine consumed INPUT
    (not a conjunct of this step's own claim).
  □ **Every CONSTRUCTION sentence checked for a leading "For since X, let …" clause** — if present, `X` is
    an `@assumption` (a construction is not automatically `@assumption`-free; e.g. I.24.1).
  □ **"either of X or Y" rendered as a DISJUNCTION** (`… = X ∨ … = Y`), not just the first side (I.24.2).
  □ No construction-byproduct incidences in any claim — only what the sentence asserts.
  □ Figural sentences translated as the FIGURE, not the consequence: "triangle=triangle" → area (parts
    separate) / congruence (bundled); "base common" → shared side; "common angle XYZ" → named `∠ x:y:z`;
    "at/under the base" → the locational identification, not the equality it implies.
  □ **A construction NAMING a figure claims the figure** (`formTriangle`/`formParallelogram` + equal
    sides), NOT the construction call's output shape — build the needed side-lines first.
  □ Every figure-area claim uses the figure's REAL corners; no region double-counted or omitted.
  □ **NO stray sorry** — every `sorry` sits in a `euclid_sentence` body or a `have := by sorry`; none in a
    tail `exact`/term (an existential witness side-condition is a `have`, not an inline `by sorry`).
  □ **`euclid_intro_sentence`/`euclid_conclude_sentence` ONLY bracket the proof** (leading / trailing) —
    NEVER mid-body. A mid-text "I say that …" (goal announcement) is **`euclid_wts "loc" "text"`**
    (structural, no claim, mid-proof-legal) — the goal is proved by the FOLLOWING sentences and assembled
    in the tail `exact`. Do NOT map it as a `euclid_sentence` carrying the goal body (assert-then-reprove),
    and do NOT demote it to intro/conclude (those are bracket-only, hard-failed mid-body by `check_faithful`).
  □ You did NOT edit any sentence's text / locator / ordering (Step-0 scaffold owns tiling).
  □ Every cited CONSTRUCTION prop has its `euclid_apply (…) as …` present in Main.

## WHAT YOU DO NOT DO
- Do NOT prove (leave `:= by sorry`; no real tactic bodies). Do NOT wire `euclid_apply (helper…)`.
- Do NOT touch the theorem signature, or any sentence's text/locator.
- Do NOT read geometry off the diagram (RULE 0) or invent facts a sentence didn't state.
- Do NOT over-read axioms — prefer the vocab; dig deeper only when a sentence can't be expressed. When a
  precedent is needed, go to the ONE canonical exemplar (this skill names it), not every done prop; and
  do NOT re-Read a file already quoted in your context — both waste API for no new information.
- Do NOT leave a stray `by sorry` in a tail term — the only sorry slots are a `euclid_sentence` body or a
  `have := by sorry`.
