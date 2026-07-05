import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step6
    (step4 : ∠ a:g:h + ∠ b:g:h > ∠ b:g:h + ∠ g:h:d)
    (step5 : ∠ a:g:h + ∠ b:g:h = ∟ + ∟) :
    ∠ b:g:h + ∠ g:h:d < ∟ + ∟ := by
  linarith

end Elements.Book1
