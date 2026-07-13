import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- ∠c₁:c:c₂ = ∠a:e:b : chain step15 (∠d:a:b = ∠c₁:c:c₂) with step14 (∠d:a:b = ∠a:e:b).
theorem helper_3_33_step16
    (a b d e c₁ c c₂ : Point)
    (hstep14 : ∠ d:a:b = ∠ a:e:b) (hstep15 : ∠ d:a:b = ∠ c₁:c:c₂) :
    ∠ c₁:c:c₂ = ∠ a:e:b := by
  euclid_finish

end Elements.Book3
