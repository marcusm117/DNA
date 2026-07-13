# Prop25 (III.25) — agent notes

## Signature fix (human-approved)
Added apex hyp `|(a─b)| = |(c─b)|` to `proposition_25` — b is Euclid's arc apex (on the
perpendicular bisector of AC). Without it, step2 (`∠a:d:b=∟`) is false for arbitrary b off AC.
**Human still needs `check_signatures.py --save`** to re-baseline the signature.

## E-construction (Case 1; Case 3 is analogous) — the hard part
Euclid's centre E = (angle-ray from A, `∠BAE=∠ABD` [1.23]) ∩ (line DB). The Phase-A map's
`have he_ex : ∃e, e≠a ∧ ∠b:a:e=∠a:b:d` was **incomplete** (angle-only, so step7 `e.onLine DB`
unprovable). Replaced with a real construction in Main:
```
euclid_apply (proposition_23' a b b a d d AB AB DB) as g   -- x=d pins g to E-side of AB
euclid_apply (line_from_points a g) as AG
have hAGDB : AG.intersectsLine DB := by sorry               -- proven, see below
euclid_apply (intersection_lines AG DB) as e
```
- `proposition_23'` (in `Book1Variants.Prop23`) fixes the side via `x` — plain `proposition_23`
  does NOT expose the side. Gives `g.onLine AB ∨ g.sameSide d AB`.
- **hAGDB (`AG.intersectsLine DB`) is TRUE and PROVEN** (NOT an @euclid_gap): the ray must cross DB
  because in △abd `∠adb=∟` ⟹ `∠abd+∠bad=∟` ⟹ the ray's angle to AC is `∠abd−∠bad<∟`, so AG≠∥DB.
  Proof (hAGDB.lean): `by_contra` (AG∥DB) → `proposition_32 b a d c AB AC DB` (triangle sum, uses
  `between a d c` as the extension, no new point) → `proposition_29''' g b a d AG DB AC` (alternate
  angle `∠g:a:d=∠a:d:b=∟`) → `euclid_finish`. Imports `Book1.Prop32.Main`, `Book1Variants.Prop29`.

## Variants live in Book1Variants/ (Prop23 → 23', Prop29 → 29'/29''/29'''/29''''/29''''').

## STATUS — ALL THREE CASES PROVEN (Phase B complete)
- Every Main node certified (`--drive` reports all-done ⟹ `--all` guaranteed). Case 3 done:
  hAG3DB (co-interior `proposition_29'''''` by_contra), step22/23 (interior sameSide),
  hEb (isosceles container: hEb_ang + hEb_tri + proposition_6), hEc (perp-bisector — bare
  euclid_finish, no prop_4 needed!), haα₃/hbα₃/hcα₃ (radii).
- **Human Phase-C TODO:** `check_signatures.py --save` (apex hyp added to proposition_25);
  `check_steps.py --save` (assumption/step signatures if changed); then `wire_main.py` +
  `check_faithful.sh Book3`.

## STATUS (checkpoint — historical)
- Signature apex fix applied (human must `check_signatures --save`).
- **Case 1 (step1–18) + Case 2 (step19–21 + hda + haα₂/hbα₂/hcα₂): FULLY CERTIFIED** (all
  backing files zero-sorry, manifest done).
- **Case 3 (he3_ex, step22, step23, haα₃/hbα₃/hcα₃): NOT STARTED.** Plan:
  - Replace `have he3_ex : ∃e … ; obtain` with the E-construction (as Case 1):
    `proposition_23' a b b a d d AB AB DB as g3` → `line_from_points a g3 as AG3` →
    `have hAG3DB : AG3.intersectsLine DB := by sorry` → `intersection_lines AG3 DB as e`.
    **But Case 3 geometry is INTERIOR** (∠abd<∠bad ⟹ E same side as b): the hAGDB-style
    intersection proof needs the CO-INTERIOR variant `proposition_29'''''`/`right_angle_cointerior`
    (needs `g3.sameSide b AC`), NOT the alternate-angle `proposition_29'''` (which needed
    `opposingSides`). Side conditions flip: step22 wants `e.sameSide b AC`, step23 `b.sameSide e AC`.
  - Circle facts haα₃/hbα₃/hcα₃: Euclid abbreviates the radii chain as "similarly", so
    `|e-a|=|e-b|=|e-c|` is NOT in Case-3 Main — must be re-derived inside the circle-fact cones
    (replicating Case 1 step9_assumption1→step15: isosceles [1.6] + SAS [1.4]).
  - ⚠ The Case-3 Main construction edit will re-stale Cases 1&2 (Main hash change) ⟹ full re-drive.
