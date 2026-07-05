import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_37_step1_adf (a b c d f : Point) (AB BC BD CD AD CF : Line)
    (h_b_AB : b.onLine AB) (h_a_AB : a.onLine AB)
    (h_d_BD : d.onLine BD) (h_b_BD : b.onLine BD)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD)
    (h_BD_BC : BD ≠ BC) (h_BC_CD : BC ≠ CD) (h_CD_BD : CD ≠ BD)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_ad : a ≠ d)
    (h_AD_BC : ¬AD.intersectsLine BC) (h_dc_AB : d.sameSide c AB)
    (h_c_CF : c.onLine CF) (h_CF_BD : ¬CF.intersectsLine BD)
    (h_f_AD : f.onLine AD) (h_f_CF : f.onLine CF) :
    between a d f := by
  euclid_finish

end Elements.Book1
