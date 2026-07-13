import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step17 (a b c e : Point) (α₁ : Circle)
    (hstep16 : e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁) :
    a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  euclid_finish

end Elements.Book3
