import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- ∠a:e:b = ∠c₁:c:c₂ : chain step24 (∠b:a:d = ∠c₁:c:c₂) with step23 (∠b:a:d = ∠a:e:b).
theorem helper_3_33_step25
    (a b d e c₁ c c₂ : Point)
    (hstep23 : ∠ b:a:d = ∠ a:e:b) (hstep24 : ∠ b:a:d = ∠ c₁:c:c₂) :
    ∠ a:e:b = ∠ c₁:c:c₂ := by
  euclid_finish

end Elements.Book3
