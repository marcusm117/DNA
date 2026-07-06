import SystemE
import Book1.Prop41.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step9 (a b c e f g : Point) (AB BC AC AE AG EF CG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_AB_ne_BC : AB ≠ BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE)
    (h_a_AG : a.onLine AG)
    (h_bet : between b e c)
    (step6 : formParallelogram f g e c AG BC EF CG)
    (hassump1 : distinctPointsOnLine e c BC)
    (hassump2 : ¬(AG.intersectsLine BC)) :
    Triangle.area △ f:e:c + Triangle.area △ f:c:g = Triangle.area △ a:e:c + Triangle.area △ a:e:c := by
  euclid_apply (proposition_41 f e c g a AG BC EF CG AE AC)
  euclid_finish

end Elements.Book1
