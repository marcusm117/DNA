import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_22_step6 (a b c d : Point)
  (hstep5 : ∠ a:d:c = ∠ b:a:c + ∠ a:c:b)
  : ∠ a:b:c + ∠ a:d:c = ∠ a:b:c + ∠ b:a:c + ∠ a:c:b := by
  linarith [hstep5]

end Elements.Book3
