import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_28_step6
    (hstep5 : ∠ a:g:h + ∠ b:g:h - ∠ b:g:h = ∠ b:g:h + ∠ g:h:d - ∠ b:g:h) :
    ∠ a:g:h = ∠ g:h:d := by
  linarith

end Elements.Book1
