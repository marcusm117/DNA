import SystemE
import Book.Prop13
import Book.Prop16
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_17_step8 (a b c : Point) (AB BC AC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB) :
    ∠ c:a:b + ∠ a:b:c < ∟ + ∟ := by
  euclid_apply (extend_point AB a b) as e
  euclid_apply (proposition_16 c a b e AC AB BC)
  euclid_apply (proposition_13 c b a e BC AB)
  euclid_apply (angle_symm c a b)
  linarith

end Elements.Book1
