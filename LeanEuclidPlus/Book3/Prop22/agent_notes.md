# Prop22 (III.22) — cyclic quadrilateral opposite angles = 2 right angles

Figure: circle ABCD, quadrilateral a,b,c,d in cyclic order. Diagonals AC, BD.
Hyps: all on circle; a,c on AC (a≠c); b,d on BD (b≠d);
  b.opposingSides d AC (¬b.sameSide d AC); a.opposingSides c BD (¬a.sameSide c BD).
Goal: (∠d:a:b + ∠b:c:d = 2∟) ∧ (∠a:b:c + ∠c:d:a = 2∟).

## STATUS: Phase B COMPLETE — 12/12 Main nodes ✓, 3/3 whole-prop checks ✓ (2026-07-11).
Depends on Book3.Prop21 (3.21) + Book1.Prop32 (1.32), both proven. Final --all witness running.
Reusable pattern discovered: the "same segment"/angle-split sameSide facts all reduce to the interior
crossing point x = AC∩BD (intersection_lines_opposing → intersection_lines; pasch_4 → between a x c &
between b x d), then pasch_2 (at each chord endpoint) + same_side_trans; euclid_finish closes given x.

## Plan / status
- step1: restate givens (distinctPointsOnLine). DONE.
- step2_assumption1 (gap): triangle abc angle sum via proposition_32. DONE.
- step2: same claim; must cite 1.32 in its OWN cone → re-apply proposition_32 (assumption binder kept, unused).
- step3_assumption1 (gap): ∃ BC, distinct b c BC ∧ a.sameSide d BC.
    PROOF: line BC = line(b,c). Crossing point x = AC∩BD (from opposingSides both ways):
      intersection_lines_opposing → x on AC,BD; pasch_4 → between a x c, between b x d.
      x∉BC (else x=c, but x≠c since between a x c... actually x between a,c on AC, c on BC; AC≠BC).
      pasch_2: between b x d, b∈BC, x∉BC → x.sameSide d BC.
      pasch_2: between c x a (=a x c reversed), c∈BC, x∉BC → x.sameSide a BC.
      same_side_trans → a.sameSide d BC.
    May just try euclid_finish given the two crossing betweenness facts + x∉BC.
- step3: ∠c:a:b = ∠b:d:c via Book3 proposition_21 (a c b d BC ABCD) + angle_symm. cites 3.21.
- step4_assumption1 (gap): ∃ AB₀, distinct a b AB₀ ∧ c.sameSide d AB₀. Same crossing-point pattern (line ab).
- step4: ∠a:c:b = ∠a:d:b via proposition_21 (c a b d AB₀ ...). cites 3.21.
- step5: ∠a:d:c = ∠b:a:c + ∠a:c:b. Needs angle-split at d: ∠a:d:c = ∠a:d:b + ∠b:d:c
    via sum_angles_onlyif (vertex d, lines DA,DC, split b) → needs a.sameSide b DC, c.sameSide b DA.
    Then substitute step3 (∠c:a:b=∠b:d:c) & step4 (∠a:c:b=∠a:d:b) + angle_symm.
- step6: +∠a:b:c both sides. arithmetic (linarith/euclid_finish) from step5.
- step7: flip of step6. arithmetic.
- step8: ∠a:b:c + ∠c:d:a = 2∟. from step7 + step2 (reorder) + angle_symm ∠a:d:c=∠c:d:a.
- step9 ("similarly"): ∠d:a:b + ∠b:c:d = 2∟.
    Derivation route (avoids full replay): split ∠dab = ∠d:a:c+∠c:a:b, ∠bcd=∠b:c:a+∠a:c:d;
    triangle acd angle sum (prop_32) + step2 + step8 ⟹ = 4∟ - 2∟ = 2∟. No citation on step9.

Diagonals cross at interior x — reusable crossing lemma pattern for the sameSide gaps.
