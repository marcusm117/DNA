import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_22_step7 (a b c d : Point)
  (hstep6 : ∠ a:b:c + ∠ a:d:c = ∠ a:b:c + ∠ b:a:c + ∠ a:c:b)
  : ∠ a:b:c + ∠ b:a:c + ∠ a:c:b = ∠ a:b:c + ∠ a:d:c := by
  linarith [hstep6]

end Elements.Book3
