import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step4
    (e₁ e₂ e₃ h k f g m : Point)
    (hassump1 : ∠ e₁:e₂:e₃ = ∠ h:k:f ∧ ∠ e₁:e₂:e₃ = ∠ g:h:m) :
    ∠ h:k:f = ∠ g:h:m := by
  linarith [hassump1.1, hassump1.2]

end Elements.Book1
