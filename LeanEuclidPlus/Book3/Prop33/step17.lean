import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- The segment α (=β) on AB with inscribed point e (=p) accepts the given angle: witnesses β=α, p=e,
-- with a,b,e on α and ∠a:e:b = ∠c₁:c:c₂ (step16).
theorem helper_3_33_step17
    (a b e c₁ c c₂ : Point) (α : Circle)
    (hacirc : a.onCircle α) (hbcirc : b.onCircle α) (hecirc : e.onCircle α)
    (hstep16 : ∠ c₁:c:c₂ = ∠ a:e:b) :
    ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂ := by
  exact ⟨α, e, hacirc, hbcirc, hecirc, hstep16.symm⟩

end Elements.Book3
