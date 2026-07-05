import SystemE
import Book.Prop35
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_37_step5 (a b c d e f : Point) (AB BC AC BD CD AD BE CF : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_ad : a ≠ d)
    (h_AD_BC : ¬AD.intersectsLine BC)
    (h_b_BE : b.onLine BE) (h_BE_AC : ¬BE.intersectsLine AC)
    (h_e_AD : e.onLine AD) (h_e_BE : e.onLine BE)
    (h_c_CF : c.onLine CF) (h_CF_BD : ¬CF.intersectsLine BD)
    (h_f_AD : f.onLine AD) (h_f_CF : f.onLine CF)
    (hassump1 : formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF) :
    Triangle.area △e:b:a + Triangle.area △a:b:c = Triangle.area △d:b:c + Triangle.area △d:c:f := by
  euclid_apply (proposition_35' e b c a d f AD BC BE AC BD CF)
  euclid_finish

end Elements.Book1
