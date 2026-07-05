import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step13
    (step11 : ∠ a:g:h = ∠ g:h:d)
    (step12 : ∠ a:g:h = ∠ e:g:b) :
    ∠ e:g:b = ∠ g:h:d := by linarith

end Elements.Book1
