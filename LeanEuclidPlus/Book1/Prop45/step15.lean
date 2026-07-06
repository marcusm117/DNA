import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step15
    (f g h m l : Point)
    (step13 : ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l)
    (step14 : ∠ m:h:g + ∠ h:g:l = ∟ + ∟) :
    ∠ h:g:f + ∠ h:g:l = ∟ + ∟ := by
  linarith

end Elements.Book1
