# Prop13 (Euclid II.13) — faithful-prove notes

**Status (2026-06-29):** Phase B COMPLETE — all 7 steps certified (SF+SP+P, zero sorry),
`--check` green (naming law, 30s caps, no stray sorry, criterion-3 deps satisfied).
Final `--all` witness launched in background.

## The proof (acute-triangle "law of cosines")
ABC acute, AD ⊥ BC with foot D between B and C.  Goal: AC² + 2·CB·BD = CB² + BA².
Pure algebra (Pythagoras ×2 + the II.7 cut identity) — NO gnomon/area machinery.

## Step recipes (all are simple leaves — no sub-cones)
- **step1** [Prop 2.7]: `euclid_apply (proposition_7 c b d BC); assumption`.
  proposition_7's conclusion instantiated at (c,b,d,BC) = step1's claim EXACTLY, so after
  euclid_apply adds the conclusion, `assumption` closes. Discharge the antecedent by providing
  `have hdist : distinctPointsOnLine c b BC := ⟨hc, hb, hne⟩` and `between c d b` (flip
  `between b d c` via `(between_symm b d c hassump1).1`). Hyps: c,b,d,BC + c.onLine BC,
  b.onLine BC, between b d c.
- **step2** (add DA²): `rw [hstep1]` — rw alone closes (LHS becomes identical to RHS).
  (NOT `rw; ring` — rw already produces `rfl` and then `ring` hits "no goals".)
- **step3** (reorder to AD²/DC²): `have h : |(d─a)|=|(a─d)| := segment_symmetric d a;
  rw [hstep2, h]; ring`.  Unlike Prop12 step3 (`exact hstep2`), Prop13 has BOTH a direction
  flip AND an order swap, so it needs `ring`, not `exact`.
- **step4** [Prop 1.47, triangle ABD]: construct DA, `euclid_apply (proposition_47 d a b DA AB BC);
  euclid_finish`.  Right angle ∠a:d:b derived from ∠a:d:c=∟ + b,d,c collinear (SMT). Full
  formTriangle hyp set (all suppliable from `--context`).
- **step5** [Prop 1.47, triangle ADC]: same, `proposition_47 d a c DA CA BC`; ∠a:d:c=∟ is the
  right angle directly. Conclusion = claim exactly.
- **step6** (substitute Pythagoras): directions differ across step3/4/5, so use
  `linarith [hstep3, hstep4, hstep5, sba, sda]` with square-symmetry links
  `sba : |(b─a)|²=|(a─b)|²`, `sda : |(d─a)|²=|(a─d)|²` (each `by rw [segment_symmetric …]`).
  Avoid `rw` chaining here — parenthesization (assoc) breaks the pattern match.
- **step7** (final rearrange): step6 sides-swapped, identical terms → `linarith [hstep6]`.

## Key gotchas
- **Phase-A gap fixed:** Main originally cited [Prop.~1.12] on the intro sentence but had NO
  construction. Added `euclid_apply (Elements.Book1.proposition_12 b c a BC) as d0` after
  `euclid_intros` + `import Book.Prop12` (mirrors Prop12's Main). `d` is already a hypothesis,
  so `d0` is a pure existence-witness recording the citation (unused elsewhere).
- **segment direction matters for `rw`/`ring`** (they see |(a─b)|² and |(b─a)|² as different
  atoms); `linarith` is the robust closer once the cross-direction squares are linked.
- The `2 * (...)` term is fine in the GOAL/conclusion (proposition_7/47 conclusions have it);
  the SMT-translator problem is only `2*x` in HYPOTHESIS position — so the algebra steps use
  Mathlib `linarith`/`ring` (import `Mathlib.Tactic.Linarith`), not euclid_finish.
- Twin = **Prop12** (II.12, obtuse case) — same proof shape; its step files were the template.
