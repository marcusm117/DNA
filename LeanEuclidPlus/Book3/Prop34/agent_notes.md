# Prop34 (III.34) — Phase B notes

Signature + all euclid_sentence CLAIMS are correct (verified). Work is realizing the
`sorry` constructions + proving each sentence.

## Node plan (in order)
- **hEF_exists** `∃ EF, b.onLine EF ∧ ¬EF.intersectsCircle ABC` — tangent at b.
  Construction: III.1 center `o`; `b≠o` (o inside, b on circle); line `BO`;
  antipode `b2` via `intersection_circle_line_extending_points ABC BO o b` (o inside) → `between b2 o b`;
  extend BO past b to `b3` so `between b2 b b3`; `proposition_11 b2 b3 b BO` → perp point `f`, `∠b2:b:f=∟`;
  `EF=line b f`; `proposition_16 b b2 o f ABC EF` → `¬EF.intersectsCircle ABC`. (needs Book3.Prop01, Book3.Prop16, Book1.Prop11)
- **hef** `∃ e f, e.onLine EF ∧ f.onLine EF ∧ between e b f` — pick two points straddling b on EF (extend_point both ways).
- **step1** repackage hEF_exists + b.onCircle.
- **hc₀ / c-construction** — needs c₀ on the circle's side of EF so the far chord intersection lands on the
  c₀ ray (else step2 `∠f:b:c=D` is the supplement). SCAFFOLD FIX may be required: realize c as the far
  intersection on the c₀-ray with `b≠c`. [1.23] construction cite must be satisfied (proposition_23 as, or proof arm).
- **hBC_int** `BC.intersectsCircle ABC` — any line through b (on circle) ≠ tangent meets circle (III.16 part 2).
- **step2** `∠f:b:c = D` — needs c on c₀-ray (see c-construction).
- **ha_exists** `∃ a, a.onCircle ABC ∧ a.opposingSides f BC` — point in alternate segment (opposite f across BC).
  Construct via center + perpendicular-diameter to BC giving one circle point per side; pick opposite-f one.
- **step3** `∠f:b:c = ∠b:a:c` — apply III.32 (proposition_32). Needs a witness for III.32's c-slot
  (a circle point opposite e across BC) — construct inside the helper (mirror of ha_exists).
  @suppress_deps_check already present (source says [1.32] but it's III.32=proposition_32).
- **step4** `∠f:b:c = D` — = step2.
- **step5** `∠b:a:c = D` — step3+step4.

## STATUS (Phase B)
DONE (certified): hEF_exists, step1, hpq, hBC_int, hc_ex, hef_choice, step2, ha_exists.
Main construction REDESIGNED (e/f-by-side via proposition_23 + hef_choice; c = far intersection via hc_ex).
Removed hb_on/hbc_ne tail haves (use hb_ABC/hbc_ne from obtains).
@suppress_deps_check moved BELOW materialized assumption haves (must be directly above sentence).
NOTE: Main builds are SLOW (~2-3min each) — every SF/SP is a full Main build. Run checks SOLO
(concurrent scaffold+check caused a 13-min lock-contention hang once).

REMAINING:
- step3_assumption2 (@assumption_gap, TRIVIAL): repackage b.onCircle∧b.onLine BC∧c.onCircle∧c.onLine BC∧b≠c.
- step3 `∠f:b:c = ∠b:a:c` via III.32 (proposition_32 b a c w e f ABC EF BC, take .1).
  Needs witness w: circle pt with w.opposingSides e BC (MIRROR of ha_exists with e instead of f).
  Decompose: step3 = container (obtain w from step3_w sub-node; euclid_apply proposition_32; euclid_finish);
  step3_w.lean = witness construction (copy ha_exists body with reference e). @suppress_deps_check covers [1.32]→III.32.
- step4 `∠f:b:c = D` = step2 (hangle_fbc / step2 in context).
- step5 `∠b:a:c = D` from step3 (∠f:b:c=∠b:a:c) + step4 (∠f:b:c=D) via euclid_finish/linarith.

## ⛔ BLOCKER on step3 — proposition_32 (III.32) signature is over-restrictive
proposition_32's antecedent has an EXTRA conjunct `∠ a:b:f = ∟` (Prop32/Main.lean:14). This pins the
alternate-segment point `a` to the ANTIPODE of b (BA ⊥ tangent = a proof artifact from Euclid's III.32
construction, NOT in his enunciation). III.34 needs the alternate-segment theorem for a GENERIC point
`a` in segment BAC (a.opposingSides f BC). The antipode CANNOT satisfy `a.opposingSides f BC` for an
OBTUSE tangent-chord angle (D>∟) — geometry: rays at 0(f), ∟(antipode), D(chord); for D>∟, f and
antipode fall on the SAME side of BC. So proposition_32 as-formalized is INAPPLICABLE to III.34's
obtuse case, and III.34 has a single uniform construction (no case split).
=> step3 (∠f:b:c = ∠b:a:c) NOT provable via proposition_32 as currently stated. Fix is at III.32's
level (drop `∠ a:b:f = ∟` → the faithful general statement; III.32's proof then needs III.21 to transfer
antipode→generic). Human/Phase-A decision on proposition_32 (also affects Prop33, the twin). REPORTED.

## RESOLVED (human-authorized 2026-07-11): III.32 signature generalized
Dropped `∠ a:b:f = ∟` from proposition_32's antecedent (Prop32/Main.lean) — it was unfaithful (pinned
`a` to the antipode; contradicts III.32's own general enunciation). step4_assumption2 (which proved that
conjunct) set to `sorry` + retagged @assumption_gap (III.32's proof now needs III.21 rework — future
Phase-B work on III.32). step3 then certified with the GENERIC `a` from ha_exists.
⚠ HUMAN TODO: check_signatures --save for III.32 (signature changed); Prop33 (twin) also depends on III.32.

9/13 → 13/13 nodes certified (step3, step4, step5 now done). step3 was the crux.
step3.lean + step3_w.lean are written (step3_w P-certified); step3's combine fails ONLY on the
proposition_32 apply (missing ∠a:b:f=∟). Once III.32 is generalized, drop the witness-w scaffolding is
unnecessary (generic a suffices) — simplify step3 to a single `euclid_apply (proposition_32 b a c w e f …)`
still needing a c-slot witness w (opposite e); keep step3_w.

## Key axioms
- center: `proposition_1 ABC : ∃ f, f.isCentre ABC`; `center_inside_circle`; `centre_unique`.
- `intersection_circle_line_extending_points α L b c : b.insideCircle α ∧ distinctPointsOnLine b c L → ∃ a, onCircle ∧ onLine ∧ between a b c`
- `proposition_11 a b c AB : distinctPointsOnLine a b AB ∧ between a c b → ∃ f, ¬f.onLine AB ∧ ∠ a:c:f = ∟`
- `proposition_16 a b d e ABC AE` (III.16): perp to diameter at end ⟹ ¬AE.intersectsCircle + every other line thru a meets circle.
- `proposition_32 b a d c e f ABCD EF BD` (III.32 alt-segment): tangent EF at b, chord BD, a opp f, c opp e ⟹ ∠f:b:d=∠b:a:d ∧ ∠e:b:d=∠d:c:b.
- `exists_point_opposite L b`, `exists_distinct_point_opposite_side L b c`, `exists_distinct_point_on_circle`.
