import SystemE
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_step6
    (d a c : Point)
    (step4 : ∠ d:a:c = ∟)
    (step5 : ∠ a:c:d = ∟)
    : ∠ d:a:c + ∠ a:c:d = ∟ + ∟ := by
  linarith

end Elements.Book3
