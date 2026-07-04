import SystemE
import Book.Prop16
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_17_step7 (a b c d : Point) (AB BC AC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    (h_dBC : d.onLine BC) (h_btw : between b c d)
    (step5 : ∠ a:c:d + ∠ a:c:b = ∟ + ∟) :
    ∠ b:a:c + ∠ a:c:b < ∟ + ∟ := by
  euclid_apply (proposition_16 a b c d AB BC AC)
  linarith

end Elements.Book1
