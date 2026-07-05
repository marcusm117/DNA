import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step4
    (hgt : ∠ a:g:h > ∠ g:h:d)
    (hstep3 : ∠ a:g:h > ∠ g:h:d → ∠ a:g:h + ∠ b:g:h > ∠ g:h:d + ∠ b:g:h) :
    ∠ a:g:h + ∠ b:g:h > ∠ b:g:h + ∠ g:h:d := by
  have h := hstep3 hgt
  linarith

end Elements.Book1
