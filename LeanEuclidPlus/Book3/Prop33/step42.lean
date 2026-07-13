import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- The segment α (=β) on AB with inscribed point h (=p) accepts the given angle: witnesses β=α, p=h,
-- with a,b,h on α and ∠a:h:b = ∠c₁:c:c₂ (step41).
theorem helper_3_33_step42
    (a b h c₁ c c₂ : Point) (α : Circle)
    (hacirc : a.onCircle α) (hb_circ : b.onCircle α) (hh_circ : h.onCircle α)
    (hstep41 : ∠ a:h:b = ∠ c₁:c:c₂) :
    ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂ := by
  exact ⟨α, h, hacirc, hb_circ, hh_circ, hstep41⟩

end Elements.Book3
