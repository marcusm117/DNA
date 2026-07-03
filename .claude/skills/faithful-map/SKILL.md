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
proof's logic requires. Consult **`faithful-patterns`** (the catalog of these shapes + exemplars). The
recurring ones:
- **Reductio / `by_contra`** — exemplars **`Book1/Prop06`** (isosceles) and **`Book2/Prop14`**
  (quadrature). Wrap the reductio body in `have habsurd : ¬(<negation of the goal>) := by intro hne …`;
  the contradiction sentence's claim is `(step_k : False)`; the closing lives in the tail
  (`exact`/contradiction from `habsurd`). A "…is not…" / "similarly, neither…" sentence carries NO
  positive claim — **RE-ROUTE its TEXT** to the branch tail or to `euclid_conclude_sentence` (keeps tiling,
  no vacuous `True`).
- **Case-split** — `by_cases h : <disjunct>` / `wlog`, one branch per case; symmetric case via a mirror
  helper or repeated structure (exemplar `Book1/Prop06`).
- **Superposition** — add `euclid_apply (superposition …) as (…)` (it births the image point + phantom
  apex); "coincide" → image equality `c' = f` (exemplar `Book/Prop08.lean`).
- **Mid-text "I say that …"** (the goal restatement, when the text places it AFTER a construction) — it is
  a NORMAL `euclid_sentence` whose claim is the GOAL BODY (exemplar `Book1/Prop10` `1.10.3`:
  `(step3 : between a d b ∧ |(a─d)| = |(d─b)|)`), and the goal closes with `exact ⟨witness, step3⟩`.
  ⛔ Do NOT demote it to `euclid_intro_sentence`/`euclid_conclude_sentence`: those are STRUCTURAL
  (claimless) and a HARD `check_faithful` gate allows them ONLY as the LEADING block (before the first
  `euclid_sentence`) / the TRAILING block (after the last). It IS provable in position — the SMT solver
  reasons from the AXIOMS in context, not from Euclid's sentence ORDER, so a fact Euclid *spells out* in
  later sentences is usually already provable now (Prop10 step3 closes by SAS from the equilateral +
  bisection facts, with steps 4/5/6 NOT needed as hyps). If you think a claim "isn't provable in
  position", TEST it (`check_step --smell`/`--provable`) BEFORE restructuring — never invent an ordering
  constraint, and never launder a dodge as a "flagged deliberate call" (the operator WILL check; green
  gates ≠ correct).
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
| "let the equilateral triangle DEF be constructed" (construction) | `formTriangle d e f DE EF DF ∧ \|(f─d)\|=\|(d─e)\| ∧ \|(f─e)\|=\|(d─e)\|` |
| "drawn parallel to AD" (construction) | `e.onLine EF ∧ ¬(EF.intersectsLine AD)` |
| "let EA, EB be joined" (construction) | `distinctPointsOnLine e a EA ∧ distinctPointsOnLine e b EB` |
| "the very thing is impossible" (reductio) | `False` (inside the frame) |
| "BE is not straight-on to CB" (a negation) | `¬ (between c b e)` |
 \|(b─c)\| = \|(b─g)\| → \|(a─l)\| = \|(b─c)\|` |

A trivially-valid claim like this last row is FAITHFUL — not a RULE-2 vacuity violation — precisely
*because Euclid states it as a sentence*. The sentence IS the claim; when Euclid invokes a Common
Notion ("things equal to the same thing…") as its own step, translate it as the implication he asserts,
not as `True`.

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
  `exact`. E.g. `use f` / `have hfa : f ≠ a := by sorry` / `exact ⟨hfa, step6⟩` (Prop09), or route the
  side-condition to a Phase-B helper à la Prop11's `between_ahb` (`refine ⟨between_ahb, step23⟩`).
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
      `import Book.PropM` at the top (the scaffold stamps only `import SystemE`, so a cited prop is an
      `unknown identifier` until imported). For a sentence needing a **frame** (reductio/`by_cases`/`wlog`)
      or a construction beyond the vocab (superposition): add the frame / `euclid_apply (superposition …)`
      — read `Book/PropNN.lean` for the shape (READING POLICY). Bodies stay `:= by sorry`.
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
    NEVER mid-body. A mid-text "I say that …" is a normal `euclid_sentence` carrying the goal body; if a
    claim seems "unprovable in position", TEST it (`--smell`/`--provable`) before restructuring — do not
    demote it to a claimless narrative line (hard-failed by `check_faithful`).
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
