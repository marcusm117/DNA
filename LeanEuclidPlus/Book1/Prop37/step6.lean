import SystemE
import Book1.Prop34.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_37_step6 (a b c d e f : Point) (AB BC AC BD CD AD BE CF : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_step4 : formParallelogram e a b c AD BC BE AC ∧
               formParallelogram d f b c AD BC BD CF) :
    Triangle.area △ a:b:c = Triangle.area △ e:a:b := by
  euclid_apply (proposition_34 e a b c AD BC BE AC AB)
  euclid_finish

end Elements.Book1
