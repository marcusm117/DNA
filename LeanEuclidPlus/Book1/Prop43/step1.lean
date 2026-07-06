import SystemE
import Book1.Prop34.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step1
    (a b c d : Point) (AD BC AB CD AC : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD)
    (h_dc : d ≠ c)
    (h_sameSide : a.sameSide b CD)
    (h_par_AD_BC : ¬AD.intersectsLine BC)
    (h_par_AB_CD : ¬AB.intersectsLine CD)
    (hassump1 : formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC)
    : Triangle.area △ a:b:c = Triangle.area △ a:c:d := by
  euclid_apply (proposition_34 d a c b AD BC CD AB AC)
  euclid_finish

end Elements.Book1
