import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_19_step8
    (h_gt : ∠ a:b:c > ∠ b:c:a)
    (h_lt : ∠ a:b:c < ∠ b:c:a) :
    False := by
  linarith

end Elements.Book1
