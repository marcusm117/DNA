import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step17
    (step15 : ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d)
    (step16 : ∠ e:g:b + ∠ b:g:h = ∟ + ∟) :
    ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := by linarith

end Elements.Book1
