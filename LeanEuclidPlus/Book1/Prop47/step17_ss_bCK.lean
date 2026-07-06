import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Ported sameSide_perp (p=b, q=a, vertex=c, r=k, L=AC, M=CK): CK ⊥ AC at c (∠a:c:k=∟),
-- ray c→b acute to c→a (∠a:c:b < ∟) ⟹ b on a's side of CK.
theorem helper_1_47_step17_ss_bCK
    (a b c k : Point) (AC CK : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hca : c ≠ a)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK) (hck : c ≠ k)
    (hACCK : AC ≠ CK)
    (hb_nAC : ¬b.onLine AC) (hb_nCK : ¬b.onLine CK)
    (h_ack : (∠ a:c:k : ℝ) = ∟)
    (h_acute : (∠ a:c:b : ℝ) < ∟) :
    b.sameSide a CK := by
  by_contra hcon
  euclid_apply (line_from_points b a) as PQ
  euclid_apply (intersection_lines PQ CK) as x
  euclid_apply (pasch_4 b x a CK PQ)
  have hbtw : between b x a := by euclid_finish
  have hperp : (∠ a:c:x : ℝ) = ∟ := by euclid_finish
  have hsplit : (∠ a:c:b : ℝ) = ∠ b:c:x + ∠ x:c:a := by
    euclid_apply (line_from_points c b) as BP
    euclid_apply (line_from_points c a) as BQ
    euclid_apply (pasch_2 a x b BQ)
    euclid_apply (pasch_2 b x a BP)
    euclid_apply (sum_angles_onlyif c b a x BP BQ)
    euclid_finish
  euclid_finish

end Elements.Book1
