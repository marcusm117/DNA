import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- ∠a:h:b = ∠c₁:c:c₂ : chain step40 (∠b:a:d = ∠c₁:c:c₂) with step39 (∠b:a:d = ∠a:h:b).
theorem helper_3_33_step41
    (a b d h c₁ c c₂ : Point)
    (hstep39 : ∠ b:a:d = ∠ a:h:b) (hstep40 : ∠ b:a:d = ∠ c₁:c:c₂) :
    ∠ a:h:b = ∠ c₁:c:c₂ := by
  euclid_finish

end Elements.Book3
