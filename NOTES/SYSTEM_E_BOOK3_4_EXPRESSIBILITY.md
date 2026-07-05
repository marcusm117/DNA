# Which Book 3 / Book 4 propositions can System E actually express?

Purpose: before investing in Book 3/4, know what System E (Avigad–Dean–Mumma 2009, as implemented
in LeanEuclid) can and cannot express.

**Revision history / honesty note.** An earlier version of this doc labelled all the tangency,
arc, and circle-segment propositions as "inexpressible / needs something added." **That was wrong**,
and wrong in a systematic way: it treated *"E has no native **sort/object** for this noun"* as
*"E can't **express** the proposition."* Those are different. The correct test (below) is logical
equivalence, and under it almost everything in Books 3–4 is expressible. The paper never enumerates
Book 3/4 props, so all per-proposition verdicts here are **derived**, not paper quotes; the paper is
quoted only for the CRITERION.

---

## The one principle that governs everything here

> A proposition is **expressible** in E iff its truth-condition can be written as a formula over E's
> actual vocabulary. If a logically-equivalent E-formula exists, the rendering is **faithful** — it
> does not matter that E lacks a sort literally named "arc," "tangent," or "segment."

This is the same rule that makes E's own `outside(a,α) := ¬inside(a,α) ∧ ¬on(a,α)` legitimate: a
*definitional abbreviation* over existing vocabulary, not a new primitive. "No native object" is
**never**, by itself, a reason to call something inexpressible.

A proposition is a **genuine gap** only if there is **no** logically-equivalent E-formula at all.

---

## The vocabulary (quoted — this is the fixed part)

From §3.1 "The language of E" (p.13–14):

> "The language of E is six-sorted, with sorts for points, lines, circles, segments, angles, and
> areas."

Relations: `on(a,L)`, `same-side(a,b,L)`, `between(a,b,c)`, `on(a,α)`, `inside(a,α)`, `center(a,α)`,
`intersects(L,M)`, `intersects(L,α)`, `intersects(α,β)`, where (§3.1):

> "by 'intersects' we really mean 'intersects transversally' … two lines intersect when they have
> exactly one point in common, and two lines, or a line and a circle, intersect when they have
> exactly two points in common."

Magnitudes (the only ones): `segment(a,b)` = length, `angle(a,b,c)` = **rectilinear** angle,
`area(a,b,c)` = **triangle** area; plus `+`, `<`, `0`, `right-angle`. There is also **superposition**
(§3.7), a construction rule for applying one figure onto another (used in I.4, I.8, and — relevant
here — III.24).

Scope claim (methodological, not linguistic) — intro p.4 / §7.1:

> "we … model many of the key **methodological features** … of the proofs found in books I through
> IV"  /  "a clean analysis of the **argumentative structure** of the proofs in Books I to IV."

---

## The re-encodings (this is what dissolves almost every apparent "gap")

| Non-native noun in the text | Logically-equivalent E rendering |
|---|---|
| **tangent / "touches"** (line–circle or circle–circle) | `touches α β := (∃p, p.onCircle α ∧ p.onCircle β) ∧ ¬ α.intersectsCircle β` (and the line version). Exactly "meets but does not cut" = one common point, since `intersects` = two. A definitional abbreviation, like `outside`. |
| **arc / circumference; equal, greater, bisected arc** | its **minor central angle** `∠BOC` (O = center, always ≤ straight). `arc = arc` ⟺ `∠ = ∠`; greater ⟺ greater; bisect-arc ⟺ bisect central angle. Major arcs need no reflex angle — major=major ⟺ minor=minor. |
| **"in the same / alternate / greater / lesser segment"** (of an inscribed *rectilinear* angle) | `same-side` / `diff-side` of the chord; "semicircle" = chord through the center. |
| **circle segment as a region; "equal segments"** | the triple (circle, chord, side). "segment₁ = segment₂" is proved by **superposition** (coincidence of circles + chords + sides) — which is how Euclid actually proves III.24 — not by a segment-area. |
| **"given / draw / cut-off a segment admitting angle C"** | construct the **circle** through the relevant endpoints on which the inscribed angle = C (III.33/34/25). The segment is that circle + a side. |
| **"equal circles"** | equal radii (`equal_circles` axiom already in E). |

Cost of these re-encodings: they are faithful (equivalent) but they are a **modeling choice** and are
often **configuration-dependent** (which side, minor vs major, auxiliary point) and **superposition-
heavy** — so the *proving* is harder than Book 1, even though *expressibility* is not the blocker.

---

## The only genuinely contestable case: curvilinear / horn angles

Def 7 "the angle of a segment" and Def 8's cousin "the angle of the semicircle" are angles between a
straight line and an **arc**. E's `angle(a,b,c)` is rectilinear (three points) — there is no native
line-vs-arc angle. The clauses that USE a horn angle *as a magnitude*:

- **III.16 tail:** "the angle of the semicircle is greater than any acute rectilinear angle, and the
  remaining (horn) angle less than any."
- **III.31 tail:** "the angle of a segment greater (than a semicircle) is greater than a right-angle …"

Whether these are a *genuine gap* is debatable, and the debate is real (this is the historical "horn
angle"):
- **Reading A (expressible):** Euclid's own adjacent clause — "no straight line can be interposed
  between the tangent and the circumference" — is a pure **line-incidence** fact E *can* state
  (`∀ L through A, L ≠ tangent → L.intersectsCircle`). The horn-magnitude sentence is arguably just
  his gloss on that, hence logically equivalent, hence expressible.
- **Reading B (gap):** taken literally as a comparison of a curvilinear magnitude against every
  rectilinear angle, there is no E term for the curvilinear magnitude, so the literal sentence has
  no E rendering.

This is the **one** place in Books 3–4 where "inexpressible" is defensible, and even here only under
the literal reading. Everything else is expressible.

---

## Legend

- ✅ **E** — truth-condition writable directly in existing vocabulary (incl. the `touches`
  abbreviation and `same-side`-encoded "segment"/"semicircle").
- ↩ **E-recast** — expressible via a logically-equivalent re-encoding from the table above
  (arc → central angle; segment-region → circle+chord+side / superposition; "a segment" →
  construct the circle). Faithful; costs a modeling choice + config-dependent, superposition-heavy
  proving.
- ❓ **horn** — contains a curvilinear-angle magnitude clause: expressible under Reading A, a gap
  under Reading B. The only contestable case.
- ⚠ **proof-cascade** — statement fine, but the proof leans on ↩ props (arc reasoning), so it
  inherits their higher proving cost (not an expressibility problem).

---

## Book 3 (37 propositions)

| # | Enunciation (abbrev.) | Class | Note |
|---|---|---|---|
| III.1 | Find the center of a circle | ✅ E | paper formalizes |
| III.2 | Chord falls inside the circle | ✅ E | paper formalizes |
| III.3 | Diameter bisects a non-central chord ⟺ ⟂ | ✅ E | |
| III.4 | Two non-central chords don't bisect each other | ✅ E | |
| III.5 | Circles that cut ⟹ different centers | ✅ E | paper formalizes |
| III.6 | Circles that **touch** ⟹ different centers | ✅ E | `touches`; note: even provable in core E as "distinct circles sharing a point ⟹ different centers" |
| III.7 | Point on diameter: radii ordering | ✅ E | segment `<` only |
| III.8 | External point: radii ordering (concave/convex) | ✅ E | concave/convex = far/near intersection point |
| III.9 | Interior point, >2 equal radii ⟹ center | ✅ E | |
| III.10 | Circles meet in ≤ 2 points | ✅ E | |
| III.11 | Internally touching: center-line hits contact | ✅ E | `touches` |
| III.12 | Externally touching: center-line thru contact | ✅ E | `touches` |
| III.13 | Circles touch in ≤ 1 point | ✅ E | `touches` |
| III.14 | Equal chords ⟺ equally far from center | ✅ E | |
| III.15 | Diameter greatest; nearer-to-center greater | ✅ E | |
| III.16 | Perp at diameter-end falls outside; no line between it and the arc; **angle of semicircle > any acute; horn < any** | ❓ horn | clauses 1–2 are ✅ E (`touches` + "every non-tangent line through A cuts"); clause 3 is the horn magnitude |
| III.17 | Draw a tangent from an external point | ✅ E | `touches` (construction) |
| III.18 | Tangent ⟹ radius ⟂ tangent at contact | ✅ E | `touches` |
| III.19 | ⟂ to tangent at contact passes thru center | ✅ E | `touches` |
| III.20 | Central angle = 2 × inscribed on same base | ✅ E | angles rectilinear; "same base" via chord + `same-side` |
| III.21 | Angles in the same segment are equal | ✅ E | "same segment" = `same-side` |
| III.22 | Cyclic quad: opposite angles = 2 right angles | ✅ E | four concyclic points |
| III.23 | No two similar unequal segments on one side | ↩ E-recast | via circle-coincidence / superposition |
| III.24 | Similar segments on equal lines are equal | ↩ E-recast | Euclid's proof *is* superposition — E has it |
| III.25 | Given a segment, complete the circle | ↩ E-recast | = circle through the given points |
| III.26 | Equal circles: equal angles on equal arcs | ↩ E-recast | arc → central angle |
| III.27 | Equal circles: angles on equal arcs are equal | ↩ E-recast | arc → central angle |
| III.28 | Equal circles: equal chords cut off equal arcs | ↩ E-recast | equal chords ⟹ equal central angle (SSS) |
| III.29 | Equal circles: equal arcs subtend equal chords | ↩ E-recast | equal central angle ⟹ equal chord (SAS) |
| III.30 | Bisect a given arc | ↩ E-recast | = bisect the central angle |
| III.31 | Angle in a semicircle = right; in greater/lesser segment; **and the angle OF a segment >/< right** | ✅ E + ❓ horn | inscribed-angle clauses ✅ (via `same-side`/diameter); "angle of a segment" clauses are horn |
| III.32 | Tangent–chord angle = inscribed in alternate seg. | ✅ E | `touches` + rectilinear + `diff-side` |
| III.33 | Draw a segment admitting a given angle | ↩ E-recast | = construct the circle admitting inscribed angle |
| III.34 | Cut off a segment admitting a given angle | ↩ E-recast | = draw the chord giving the inscribed angle |
| III.35 | Intersecting chords: rect = rect | ✅ E | `rectangle_area` (Book 2) |
| III.36 | Secant·external = tangent² | ✅ E | `touches` + rectangle/square |
| III.37 | Converse of III.36 (⟹ touches) | ✅ E | `touches` |

**Book 3:** genuinely-contestable only at **III.16** and **III.31** (horn clauses). Everything else is
✅ E or ↩ E-recast — expressible and faithful, with the arc/segment ones costing more to *prove*.

---

## Book 4 (16 propositions)

Defs 1–7 (inscribe/circumscribe via "angles/sides touch"): vertex-on-circle ✅; side-tangent uses
`touches` ✅. All expressible.

| # | Enunciation (abbrev.) | Class | Note |
|---|---|---|---|
| IV.1 | Insert a chord = given line (≤ diameter) | ✅ E | |
| IV.2 | Inscribe a triangle equiangular to a given one | ✅ E | ⚠ proof uses III.32 |
| IV.3 | Circumscribe such a triangle about a circle | ✅ E | `touches`; ⚠ III.32 |
| IV.4 | Inscribe a circle in a triangle (incircle) | ✅ E | `touches` (tangent to 3 sides) |
| IV.5 | Circumscribe a circle about a triangle | ✅ E | |
| IV.6 | Inscribe a square in a circle | ✅ E | |
| IV.7 | Circumscribe a square about a circle | ✅ E | `touches` |
| IV.8 | Inscribe a circle in a square | ✅ E | `touches` |
| IV.9 | Circumscribe a circle about a square | ✅ E | |
| IV.10 | Isosceles triangle, base angles = 2 × apex | ✅ E | golden cut (II.11) is E; ⚠ proof uses III.32/37 |
| IV.11 | Inscribe a regular pentagon | ✅ E | ⚠ proof leans on III.26–29 (↩ recast) |
| IV.12 | Circumscribe a regular pentagon | ✅ E | `touches`; ⚠ arcs |
| IV.13 | Inscribe a circle in a regular pentagon | ✅ E | `touches` |
| IV.14 | Circumscribe a circle about a regular pentagon | ✅ E | |
| IV.15 | Inscribe a regular hexagon | ✅ E | ⚠ proof uses arc reasoning |
| IV.16 | Inscribe a regular 15-gon | ✅ E | ⚠ proof uses III.30 (arc bisection, ↩) + arc arithmetic |

**Book 4:** every proposition is ✅ E. The regular-polygon proofs (IV.11/12/15/16) inherit the ↩
arc-recast cost through III.26–30, but nothing is inexpressible.

---

## Corrected bottom line

- **Expressibility is essentially total across Books 3–4.** The earlier "arc gap" and "segment gap"
  were the same mistake as the "touch gap": confusing *no native sort* with *inexpressible*. Under
  logical equivalence, arcs → central angles, segments → circle+chord+side (+superposition),
  tangency → a definitional predicate.
- **The real barrier is not language but (a) a modeling choice** — you must decide the arc/segment
  encoding up front and it's config-dependent — **and (b) proving cost:** superposition-heavy,
  case-heavy, Book-2-and-then-some. That's where the effort goes, not in "can we even state it."
- **The single contestable gap** is the curvilinear **horn angle** (Def 7; III.16 tail; III.31
  tail): expressible if you read Euclid's horn clauses as glosses on the line-incidence facts he
  states alongside them, a genuine gap if you insist on the literal curvilinear magnitude.
- **Caveat that reconciles this with the paper's careful wording:** E can express the *theorems* of
  Books 3–4, but the recasts *restructure* Euclid's arc-as-first-class-magnitude reasoning. So E is
  faithful to the theorems, and only loosely faithful to the arc *method* — which is exactly why the
  paper claims "methodological features" and "argumentative structure," not full method-level
  fidelity, for Books III–IV.
