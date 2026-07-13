import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- ∠d:a:b = ∠c₁:c:c₂ : the constructed angle (Prop 1.23, construction arm in Main) — restated given.
theorem helper_3_33_step15
    (a b d c₁ c c₂ : Point)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) :
    ∠ d:a:b = ∠ c₁:c:c₂ := by
  euclid_finish

end Elements.Book3
