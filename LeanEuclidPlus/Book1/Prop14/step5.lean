import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_14_step5 (a b c d e : Point)
  (h4 : ∠ c:b:a + ∠ a:b:e = ∠ c:b:a + ∠ a:b:d)
  : ∠ a:b:e = ∠ a:b:d := by
  linarith

end Elements.Book1
