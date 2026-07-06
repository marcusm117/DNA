import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Ported from Book/Prop47.lean `helper_47_sameSide_perp` (p=c, q=a, b=b, r=f, L=AB, M=BF):
-- BF ⊥ AB at b (∠a:b:f = ∟), ray b→c acute to b→a (∠c:b:a < ∟) ⟹ c on a's side of BF.
theorem helper_1_47_step8_hC11
    (a b c f : Point) (AB BF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BF : b.onLine BF) (hf_BF : f.onLine BF) (hfb : f ≠ b)
    (hABBF : AB ≠ BF)
    (hc_nAB : ¬c.onLine AB) (hc_nBF : ¬c.onLine BF)
    (h_abf : (∠ a:b:f : ℝ) = ∟)
    (h_acute : (∠ a:b:c : ℝ) < ∟) :
    c.sameSide a BF := by
  by_contra hcon
  euclid_apply (line_from_points c a) as PQ
  euclid_apply (intersection_lines PQ BF) as x
  euclid_apply (pasch_4 c x a BF PQ)
  have hbtw : between c x a := by euclid_finish
  have hperp : (∠ a:b:x : ℝ) = ∟ := by euclid_finish
  have hsplit : (∠ c:b:a : ℝ) = ∠ c:b:x + ∠ x:b:a := by
    euclid_apply (line_from_points b c) as BP
    euclid_apply (line_from_points b a) as BQ
    euclid_apply (pasch_2 a x c BQ)
    euclid_apply (pasch_2 c x a BP)
    euclid_apply (sum_angles_onlyif b c a x BP BQ)
    euclid_finish
  euclid_finish

end Elements.Book1
