import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Ported from `helper_47_sameSide_perp` (p=a, q=c, b=b, r=d, L=BC, M=BD):
-- BD ⊥ BC at b (∠c:b:d = ∟), ray b→a acute to b→c (∠a:b:c < ∟) ⟹ a on c's side of BD.
theorem helper_1_47_step8_hA11
    (a b c d : Point) (BC BD : Line)
    (hc_BC : c.onLine BC) (hb_BC : b.onLine BC) (hbc : b ≠ c)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD) (hbd : b ≠ d)
    (hBCBD : BC ≠ BD)
    (ha_nBC : ¬a.onLine BC) (ha_nBD : ¬a.onLine BD)
    (h_cbd : (∠ c:b:d : ℝ) = ∟)
    (h_acute : (∠ a:b:c : ℝ) < ∟) :
    a.sameSide c BD := by
  by_contra hcon
  euclid_apply (line_from_points a c) as PQ
  euclid_apply (intersection_lines PQ BD) as x
  euclid_apply (pasch_4 a x c BD PQ)
  have hbtw : between a x c := by euclid_finish
  have hperp : (∠ c:b:x : ℝ) = ∟ := by euclid_finish
  have hsplit : (∠ a:b:c : ℝ) = ∠ a:b:x + ∠ x:b:c := by
    euclid_apply (line_from_points b a) as BP
    euclid_apply (line_from_points b c) as BQ
    euclid_apply (pasch_2 c x a BQ)
    euclid_apply (pasch_2 a x c BP)
    euclid_apply (sum_angles_onlyif b a c x BP BQ)
    euclid_finish
  euclid_finish

end Elements.Book1
