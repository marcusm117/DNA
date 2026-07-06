import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step8 (a b c e : Point) (AB BC : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_AB_ne_BC : AB ≠ BC)
    (h_bet : between b e c)
    (step7 : Triangle.area △ a:b:e = Triangle.area △ a:e:c) :
    Triangle.area △ a:b:c = Triangle.area △ a:e:c + Triangle.area △ a:e:c := by
  have h_a_not_BC : ¬a.onLine BC := by
    intro h
    have : AB = BC := by euclid_apply (two_points_determine_line a b AB BC); euclid_finish
    exact h_AB_ne_BC this
  euclid_apply (sum_areas_if b c e a BC)
  euclid_finish

end Elements.Book1
