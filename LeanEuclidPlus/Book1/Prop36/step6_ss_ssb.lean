import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_36_step6_ss_ssb (a b c d e h : Point) (AH BG AB CD CH : Line)
  (h_a_AH : a.onLine AH) (h_e_AH : e.onLine AH) (h_h_AH : h.onLine AH)
  (h_b_BG : b.onLine BG) (h_c_BG : c.onLine BG)
  (h_d_AH : d.onLine AH)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
  (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD) (h_d_ne_c : d ≠ c)
  (h_ss_ab_CD : a.sameSide b CD)
  (h_ab_ne_cd : ¬AB.intersectsLine CD)
  (h_c_CH : c.onLine CH) (h_h_CH : h.onLine CH)
  (h_par : ¬AH.intersectsLine BG)
  (h_dp_eh_AH : distinctPointsOnLine e h AH)
  (h_dp_bc_BG : distinctPointsOnLine b c BG)
  (h_step6_ss_ssa : e.sameSide a CH)
  (h_bet : between a e h)
  (h_bet_adh : between a d h) :
  a.sameSide b CH := by
  euclid_assert ¬(a.onLine CH)
  euclid_assert ¬(b.onLine CH)
  euclid_assert (a.sameSide b CH)
  assumption

end Elements.Book1
