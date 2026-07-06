import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step8
    (f g k h m : Point)
    (step6 : ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m)
    (step7 : ∠ f:k:h + ∠ k:h:g = ∟ + ∟) :
    ∠ k:h:g + ∠ g:h:m = ∟ + ∟ := by
  linarith

end Elements.Book1
