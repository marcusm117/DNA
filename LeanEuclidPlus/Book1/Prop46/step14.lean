import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step14
    (a b d e : Point)
    (step12 : ∠ b:a:d + ∠ a:d:e = ∟ + ∟)
    (step13 : ∠ b:a:d = ∟) :
    ∠ a:d:e = ∟ := by
  linarith

end Elements.Book1
