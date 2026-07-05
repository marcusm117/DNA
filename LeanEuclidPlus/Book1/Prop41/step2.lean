import SystemE
import Book.Prop37
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_41_step2 (a b c e : Point) (AE BC AB CD AC BE CE : Line)
    (h_a_AE : a.onLine AE) (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_c_CD : c.onLine CD) (h_sameSide : a.sameSide b CD)
    (h_e_AE : e.onLine AE)
    (h_e_BE : e.onLine BE) (h_b_BE : b.onLine BE) (h_eb : e ≠ b)
    (h_c_CE : c.onLine CE) (h_e_CE : e.onLine CE)
    (h_BE_BC : BE ≠ BC) (h_BC_CE : BC ≠ CE) (h_CE_BE : CE ≠ BE)
    (h_par_AB_CD : ¬AB.intersectsLine CD)
    (step1 : distinctPointsOnLine a c AC)
    (hassump1 : distinctPointsOnLine b c BC)
    (hassump2 : ¬(AE.intersectsLine BC)) :
    Triangle.area △ a:b:c = Triangle.area △ e:b:c := by
  by_cases h : a = e
  · rw [h]
  · euclid_apply (proposition_37' a b c e AB BC AC BE CE AE)
    euclid_finish

end Elements.Book1
