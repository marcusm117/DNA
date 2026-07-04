import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step5 (a b c d : Point) (BC AC : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hBCAC : BC ≠ AC)
    (hbetween : between a d c)
    (hstep3 : ∠ a:d:b > ∠ d:c:b)
    (hstep4 : ∠ a:d:b = ∠ a:b:d)
    : ∠ a:b:d > ∠ b:c:a := by
  have heq : ∠ d:c:b = ∠ b:c:a := by euclid_finish
  linarith

end Elements.Book1
