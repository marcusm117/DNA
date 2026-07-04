import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_17_step3 (a b c d : Point)
    (step2 : ∠ a:c:d > ∠ a:b:c) : ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ a:c:b := by
  linarith

end Elements.Book1
