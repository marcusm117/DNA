import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step8 (a b d p : Point)
    (hstep6 : ∠ d:p:b > ∠ d:a:p)
    (hstep7 : ∠ d:a:p = ∠ d:b:p) :
    ∠ d:p:b > ∠ d:b:p := by
  linarith

end Elements.Book3
