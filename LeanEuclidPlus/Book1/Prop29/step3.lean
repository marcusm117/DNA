import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step3 :
    ∠ a:g:h > ∠ g:h:d → ∠ a:g:h + ∠ b:g:h > ∠ g:h:d + ∠ b:g:h := by
  intro h
  linarith

end Elements.Book1
