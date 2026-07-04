import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_15_step5
  (c e a d b : Point)
  (hstep4 : ∠ c:e:a + ∠ a:e:d = ∠ a:e:d + ∠ d:e:b)
  : ∠ c:e:a + ∠ a:e:d - ∠ a:e:d = ∠ a:e:d + ∠ d:e:b - ∠ a:e:d := by
  linarith

end Elements.Book1
