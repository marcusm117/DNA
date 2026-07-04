import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_17_step4 (a b c d : Point) (AB BC AC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    (step3 : ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ a:c:b) :
    ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ b:c:a := by
  have h_sym : ∠ a:c:b = ∠ b:c:a := by
    apply angle_symm
    constructor <;> euclid_finish
  linarith

end Elements.Book1
