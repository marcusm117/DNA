import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_37_step4 (a b c d e f : Point) (AB BC AC BD CD AD BE CF : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_d_BD : d.onLine BD) (h_b_BD : b.onLine BD)
    (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD)
    (h_BD_BC : BD ≠ BC) (h_BC_CD : BC ≠ CD) (h_CD_BD : CD ≠ BD)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_ad : a ≠ d)
    (h_AD_BC : ¬AD.intersectsLine BC) (h_dc_AB : d.sameSide c AB)
    (h_b_BE : b.onLine BE) (h_BE_AC : ¬BE.intersectsLine AC)
    (h_e_AD : e.onLine AD) (h_e_BE : e.onLine BE)
    (h_c_CF : c.onLine CF) (h_CF_BD : ¬CF.intersectsLine BD)
    (h_f_AD : f.onLine AD) (h_f_CF : f.onLine CF)
    (h_step1 : between d a e ∧ between a d f)
    (h_step2 : b.onLine BE ∧ e.onLine BE ∧ ¬BE.intersectsLine AC)
    (h_step3 : c.onLine CF ∧ f.onLine CF ∧ ¬CF.intersectsLine BD) :
    formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF := by
  have h4a : formParallelogram e a b c AD BC BE AC := by euclid_finish
  have h4b : formParallelogram d f b c AD BC BD CF := by euclid_finish
  exact ⟨h4a, h4b⟩

end Elements.Book1
