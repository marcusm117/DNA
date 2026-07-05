import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_37_step1 (a b c d e f : Point) (AB BC AC BD CD AD BE CF : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_d_BD : d.onLine BD) (h_b_BD : b.onLine BD) (h_db : d ≠ b)
    (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD)
    (h_BD_BC : BD ≠ BC) (h_BC_CD : BC ≠ CD) (h_CD_BD : CD ≠ BD)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_ad : a ≠ d)
    (h_AD_BC : ¬AD.intersectsLine BC) (h_dc_AB : d.sameSide c AB)
    (h_b_BE : b.onLine BE) (h_BE_AC : ¬BE.intersectsLine AC)
    (h_e_AD : e.onLine AD) (h_e_BE : e.onLine BE)
    (h_c_CF : c.onLine CF) (h_CF_BD : ¬CF.intersectsLine BD)
    (h_f_AD : f.onLine AD) (h_f_CF : f.onLine CF) :
    between d a e ∧ between a d f := by
  have step1_dae : between d a e := by sorry
  have step1_adf : between a d f := by sorry
  exact ⟨step1_dae, step1_adf⟩

end Elements.Book1
