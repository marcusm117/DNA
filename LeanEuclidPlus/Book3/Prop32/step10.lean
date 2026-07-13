import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_32_step10 (a' b d f : Point)
    (step9 : ∠ a':b:f = ∠ b:a':d + ∠ a':b:d) :
    ∠ a':b:f - ∠ a':b:d = ∠ b:a':d := by
  linarith

end Elements.Book3
