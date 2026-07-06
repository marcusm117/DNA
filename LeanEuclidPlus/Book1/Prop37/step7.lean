import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_37_step7 (a b c d e f : Point) (AB BC AC BD CD AD BE CF : Line)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_d_BD : d.onLine BD) (h_b_BD : b.onLine BD)
    (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD)
    (h_BD_BC : BD ≠ BC) (h_BC_CD : BC ≠ CD) (h_CD_BD : CD ≠ BD)
    (h_d_AD : d.onLine AD) (h_ad : a ≠ d)
    (h_AD_BC : ¬AD.intersectsLine BC) (h_dc_AB : d.sameSide c AB)
    (h_c_CF : c.onLine CF) (h_CF_BD : ¬CF.intersectsLine BD)
    (h_f_AD : f.onLine AD) (h_f_CF : f.onLine CF)
    (h_step4 : formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF) :
    Triangle.area △ d:b:c = Triangle.area △ f:d:c := by
  euclid_apply (proposition_34 f d c b AD BC CF BD CD)
  euclid_finish

end Elements.Book1
