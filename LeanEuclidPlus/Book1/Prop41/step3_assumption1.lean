import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_41_step3_assumption1 (a b c d : Point) (AE BC AB CD AC : Line)
    (h_a_AE : a.onLine AE) (h_d_AE : d.onLine AE)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD)
    (h_dc : d ≠ c)
    (h_sameSide : a.sameSide b CD)
    (h_par_AE_BC : ¬AE.intersectsLine BC)
    (h_par_AB_CD : ¬AB.intersectsLine CD)
    (step1 : distinctPointsOnLine a c AC) :
    Triangle.area △ a:b:c = Triangle.area △ a:c:d := by
  euclid_apply (proposition_34 d a c b AE BC CD AB AC)
  euclid_finish

end Elements.Book1
