# Book 3 Vocabulary & Convention Primer

The single source of truth for how Book-3 (circle) vocabulary is rendered in System E.
The `faithful-signature` and `faithful-map` skills both reference this file so every prop is
rendered **identically**.

## Governing principle — ZERO System E changes

Nothing is added to System E for Book 3. Every circle concept is either (a) a **native predicate**
already in `SystemE`, or (b) an **inline convention** — a fixed formula over native vocabulary that
you write out in full each time (never a new `def`). This is the same status as E's own
`outside(a,α) := ¬inside ∧ ¬on`: a definitional abbreviation, not a primitive. We keep it inline
(not a Lean `def`) to avoid giving the SMT backend a new symbol it can't unfold — the solver only
ever sees primitives it already handles. See `SYSTEM_E_BOOK3_4_EXPRESSIBILITY.md` for the derivation.

---

## ⚑ PROOF-FAITHFULNESS — the OVERRIDING criterion (operator, 2026-07-05)

The paper's whole point is that Euclid's **PROOF** is faithfully formalized: **every single sentence
Euclid writes maps to a step in the proof.** The signature must therefore be stated at the generality
Euclid's PROOF supports — **no more**.

- **DO NOT over-generalize.** A `∀`-over-all-circle-points, or a global max/min, is WRONG if Euclid
  argues about **specific named points** (B, C, G): his sentence "FB > FC" then has no named FB, FC to
  map onto, and the statement may be unprovable by his method. Prefer Euclid's **specific-figure**
  statement — his named points as binders + his ordering hypotheses — over a slick universal.
- **Admit all of Euclid's CASES.** If the proof splits ("So let another … be inflected", "similarly…",
  a second configuration), the signature must be general enough that every case-block's sentences map —
  but no more general than that.
- **When enunciation-generality and proof-faithfulness conflict, PROOF-FAITHFULNESS WINS.** State what
  Euclid actually proves, sentence-for-sentence, not the slickest logically-equivalent form.

Check every signature against the PROOF text (not just the enunciation): could each proof sentence be
mapped to a step whose claim this statement supports? If not, restate.

## Native predicates — use directly (nothing to define)

| Text concept | Native rendering |
|---|---|
| point on the circle / "on the circumference" (a **locus**) | `a.onCircle α` |
| point inside / outside the circle | `a.insideCircle α` / `a.outsideCircle α` |
| the center | `a.isCentre α` |
| a straight-line **cuts** a circle (2 pts) | `L.intersectsCircle α` |
| two circles **cut** (2 pts) | `α.intersectsCircle β` |
| a chord / "straight-line in the circle" | a `Line` with two points `.onCircle α` (no special predicate) |
| two distinct points determine a line | `distinctPointsOnLine a b L` |
| on a line / same side / opposite side / between | `a.onLine L` / `a.sameSide b L` / `a.opposingSides b L` / `between a b c` |
| length, angle, right-angle | `\|(a─b)\|`, `∠ a:b:c`, `∟` |
| **"for they are radii" ⟹ equal** | `point_on_circle_onlyif` : `isCentre o α → b.onCircle α → c.onCircle α → \|(o─b)\| = \|(o─c)\|`. Radius is a length, **not** an object. |
| construct a circle from center + a point on it | `circle_from_points a b` : `a ≠ b → ∃ α, a.isCentre α ∧ b.onCircle α` |
| "equal circles" | `equal_circles` axiom (equal radii) — never a circle-area |

⚠ **"circumference" is overloaded.** As a *locus* ("a point on the circumference") it is `onCircle`
— native, above. As a *magnitude* ("equal / greater / bisected circumferences", i.e. an **arc**) it is
a central angle — see the conventions below. Decide which per sentence.

---

## Inline conventions — write the formula out in full (NO new vocab)

> ⚠ **`intersectsCircle` is NOT "shares a point" / nonempty intersection.** The elim axiom gives only
> `intersects → ∃ common point`; the CONVERSE is not an axiom. So `¬intersects` does NOT mean "no common
> point" — it means "does not CROSS." Hence `(∃ common point) ∧ ¬intersects` is NOT a contradiction; it is
> exactly the 1-common-point (tangent) case. Trichotomy: 0 pts → ¬intersects,¬common; 1 pt (tangent) →
> ¬intersects,✓common (= `touches`); 2 pts (crossing) → intersects.
>
> **What `intersectsCircle` means (verified against the axioms, not just the paper).** It is `opaque`;
> its meaning is fixed by its intro/elim axioms = **transversal boundary-crossing** (Avigad §3.1: "exactly
> two points in common"). NOT interior-overlap, NOT "share ≥1 point". Line–circle elim gives **two
> distinct** common points (`intersections_circle_line`); intro needs an interior/opposite-sides witness.
> Circle–circle intro needs a strict inside-AND-outside witness pair (`intersection_circle_circle_1`: a
> point of α inside β and a point of α outside β) = boundaries properly cross. So `¬intersectsCircle ∧
> (∃ common point)` = "meet but don't cross" = tangency. ✓ correct.
> ⚠ **Proving caveat (not an expressibility problem):** the circle–circle axioms are weaker than
> line–circle — elim exposes only ONE witness point and there is NO "one common point ⟹ ¬intersects"
> axiom. So `¬α.intersectsCircle β` must be established from explicit geometric witnesses in Phase B
> (III.6/11/12/13); the solver won't derive it for free.

### `touches` — line–circle (tangent)
> `(∃ p, p.onLine L ∧ p.onCircle α) ∧ ¬ L.intersectsCircle α`

"meets but does not cut" = exactly 1 common point (since `intersectsCircle` = exactly 2).

### `touches` — circle–circle (tangent)
> `(∃ p, p.onCircle α ∧ p.onCircle β) ∧ ¬ α.intersectsCircle β`

### diameter (chord through the center)
"AB is a diameter of α" >
> `∃ o, o.isCentre α ∧ between a o b ∧ a.onCircle α ∧ b.onCircle α`

(optional readability convenience; always inlineable. Used by ~9 props.)

### semicircle ("an angle in a semicircle")
The chord subtending the inscribed angle **is a diameter** — i.e. passes through the center. Render
"angle ∠a:c:b is in a semicircle" as: `c.onCircle α` with `ab` a diameter (center between `a` and `b`).
There is no `semicircle` object.

### arc / "circumference" as a MAGNITUDE
An arc `AB` is its **minor central angle** `∠ a:O:b` (O = the center). Then:
- `arc AB = arc CD`  ⟺  `∠ a:O:b = ∠ c:O':d`
- `arc AB > arc CD`  ⟺  `∠ a:O:b > ∠ c:O':d`
- "bisect arc AB"    ⟺  bisect the central angle `∠ a:O:b`

Major arcs need no reflex angle: major = major ⟺ the minor complements are equal. **Config-dependent**
— you must name the center point and (implicitly) take the minor angle. Used by III.26–30.

### "in the same / alternate / greater / lesser segment" (of an inscribed rectilinear angle)
The **apex's side of the chord**:
- "same segment" → apex `sameSide` the chord
- "alternate segment" → apex `opposingSides` the chord

There is no `segment` object; the inscribed angle is a plain `∠` on three points.

### "similar segments equal" / "no two similar segments" (III.23, III.24)
Proved by **superposition** (coincidence of circle + chord + side) — the way Euclid actually argues
III.24. Not a segment-area. (A map-phase concern; the enunciation still states it via the circle/chord/side.)

### "a segment admitting a given angle" (III.25, III.33, III.34)
The **circle** on which the inscribed angle equals the given angle; the "segment" is that circle plus a
side. Construction goal ⟹ existential over the circle.

---

## Goal shapes (what the theorem concludes)

- **Construction props** (III.1 find-center, III.17 draw-tangent, III.25/30/33/34) → **existential**
  goal: `∃ <constructed object>, <its properties>`. (cf. Book 1 `proposition_1`:
  `… → ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|`.)
- **Property / theorem props** (III.2 chord-inside, III.20 central=2·inscribed) → a property or equality
  goal, no `∃`.
- **Biconditional props** ("… and conversely …", III.3) → a **conjunction of the two directions**:
  `(P → Q) ∧ (Q → P)`, or the two implications as the enunciation phrases them.

The signature translates the **enunciation** (split.json index 0 `intro`), NOT the proof body. The
diagram is for **label resolution only** — never a source of the statement.

---

## The horn / curvilinear-angle clauses — the ONE open decision

Only the **tails** of **III.16** and **III.31** compare a curved-vs-straight ("horn") angle magnitude,
which E cannot express. DECISION PENDING (operator): either
- **Reading A** — render the adjacent line-incidence fact Euclid states alongside
  (`∀ L through the contact point, L ≠ tangent → L.intersectsCircle α`) and treat the horn sentence as
  its gloss; or
- **Reading B** — mark those specific tail clauses out-of-scope (the rest of III.16/III.31 is fully
  expressible).

Do not formalize a horn clause until this is settled. (Does not affect the III.1/2/3 pilot.)

---

## Naming conventions

- **Points** → lowercase Euclid label: `A → a`, `B → b`, `F → f`.
- **Lines** → the two-letter Euclid label uppercased: `AB → AB`, `CD → CD` (`_ : Line`).
- **Circles** → the Euclid label as an uppercase identifier, matching Book-1 style (`BCD`, `ACE`).
  A given circle is just `ABC : Circle`. **Do NOT force three naming points onto it.** Euclid's
  "ABC" is nomenclature, not a logical requirement — a `Circle` is its own object. Introduce a point
  with `_.onCircle ABC` **only when the statement or goal actually references that point** (e.g. the
  two chord-endpoints), and add distinctness (`a ≠ b`) only where the statement needs it. A signature
  must carry NO dead hypothesis: if a point never appears in a hyp/goal that uses it, drop it.
  (So III.1 "find the center" is simply `∀ (ABC : Circle), ∃ f, f.isCentre ABC` — zero points.)
  The `α`/`β` greek names are only for quoting axioms, not for a concrete given circle.

## Worked calibration example — III.2

Enunciation: *"If two points are taken at random on the circumference of a circle, then the
straight-line joining the points will fall inside the circle. Let ABC be a circle, and let two
points A and B be taken at random on its circumference…"*

- given: circle `ABC` and the two random points `a b : Point` on it (only the points the statement
  uses — no dead third naming point)
- "on the circumference" = **locus** → `onCircle` (not an arc)
- "joining line falls inside" = every point strictly between them is inside:
  `∀ p : Point, between a p b → p.insideCircle ABC`

Final (verified — compiles via `check_step --signature`):
```
theorem proposition_2 : ∀ (a b : Point) (ABC : Circle),
  a.onCircle ABC ∧ b.onCircle ABC ∧ a ≠ b →
  ∀ p : Point, between a p b → p.insideCircle ABC
```

---

## Book-3 file conventions

- Signature stub = **`import SystemE` + `namespace Elements.Book3`** + the theorem, body `:= by sorry`.
  **NO `open Elements.Book1`** — the statement cites no Book-1 lemma, and with only `import SystemE`
  the `Elements.Book1` namespace isn't populated yet (`open` → "unknown namespace"). The `open` +
  cited-prop imports are added LATER by the map/assemble step, when the proof body needs them.
- `theorem proposition_N : ∀ (binders), <given hyps> → <goal> := by sorry` (body stays `sorry` in Phase A).
- Verify the statement compiles: `python3 scripts/check_step.py Book3/PropNN --signature`.
- Layout: `Book3/PropNN/Main.lean` + `Book3/PropNN/split.json`; helpers `helper_3_N_stepN`.
