import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- ∠b:a:d = ∠c₁:c:c₂ : angle symmetry of the constructed angle ∠d:a:b = ∠c₁:c:c₂ (Prop 1.23).
theorem helper_3_33_step24
    (a b d c₁ c c₂ : Point)
    (hne : a ≠ b) (hadd : d ≠ a) (hdab : ∠ d:a:b = ∠ c₁:c:c₂) :
    ∠ b:a:d = ∠ c₁:c:c₂ := by
  euclid_finish

end Elements.Book3
