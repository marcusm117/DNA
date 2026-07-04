import SystemE
import Book.Prop05
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_18_step4 (a b d : Point) (AB BC AC BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hbetween : between a d c)
    (hassump1 : |(a─b)| = |(a─d)|)
    : ∠ a:d:b = ∠ a:b:d := by
  euclid_apply (proposition_5' a b d AB BD AC)
  linarith

end Elements.Book1
