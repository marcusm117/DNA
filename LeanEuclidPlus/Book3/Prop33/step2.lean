import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- ∠b:a:d < ∟ : ∠b:a:d = ∠c₁:c:c₂ (step1) and ∠c₁:c:c₂ < ∟ (acute case).
theorem helper_3_33_step2
    (a b d c₁ c c₂ : Point)
    (step1 : ∠ b:a:d = ∠ c₁:c:c₂) (hacute : ∠ c₁:c:c₂ < ∟) :
    ∠ b:a:d < ∟ := by
  linarith

end Elements.Book3
