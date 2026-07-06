import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Ported sameSide_perp (p=a, q=b, vertex=c, r=e, L=BC, M=CE): CE ⊥ BC at c (∠b:c:e=∟),
-- ray c→a acute to c→b (∠a:c:b < ∟) ⟹ a on b's side of CE.
theorem helper_1_47_step17_ss_aCE
    (a b c e : Point) (BC CE : Line)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hcb : c ≠ b)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE) (hce : c ≠ e)
    (hBCCE : BC ≠ CE)
    (ha_nBC : ¬a.onLine BC) (ha_nCE : ¬a.onLine CE)
    (h_bce : (∠ b:c:e : ℝ) = ∟)
    (h_acute : (∠ a:c:b : ℝ) < ∟) :
    a.sameSide b CE := by
  by_contra hcon
  euclid_apply (line_from_points a b) as PQ
  euclid_apply (intersection_lines PQ CE) as x
  euclid_apply (pasch_4 a x b CE PQ)
  have hbtw : between a x b := by euclid_finish
  have hperp : (∠ b:c:x : ℝ) = ∟ := by euclid_finish
  have hsplit : (∠ a:c:b : ℝ) = ∠ a:c:x + ∠ x:c:b := by
    euclid_apply (line_from_points c a) as BP
    euclid_apply (line_from_points c b) as BQ
    euclid_apply (pasch_2 b x a BQ)
    euclid_apply (pasch_2 a x b BP)
    euclid_apply (sum_angles_onlyif c a b x BP BQ)
    euclid_finish
  euclid_finish

end Elements.Book1
