import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- ∠b:a:d = ∠c₁:c:c₂ : angle symmetry of the constructed angle ∠d:a:b = ∠c₁:c:c₂ (Prop 1.23,
-- construction arm in Main).
theorem helper_3_33_step1
    (a b d c₁ c c₂ : Point)
    (hne : a ≠ b) (hadd : d ≠ a) (hdab : ∠ d:a:b = ∠ c₁:c:c₂) :
    ∠ b:a:d = ∠ c₁:c:c₂ := by
  euclid_finish

end Elements.Book3
