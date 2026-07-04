import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_16_h1 (a b c d : Point) (AB BC AC : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_step14 : ∠ a:c:d > ∠ a:b:c) :
    ∠ a:c:d > ∠ c:b:a := by
  have h_eq : ∠ a:b:c = ∠ c:b:a := by euclid_finish
  linarith

end Elements.Book1
