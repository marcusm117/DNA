import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step12
    (ABC DEF : Circle) (p b : Point)
    (hABCneDEF : ABC ≠ DEF)
    (hbABC : b.onCircle ABC) (hbDEF : b.onCircle DEF)
    (step10 : p.isCentre ABC ∧ p.isCentre DEF)
    : ¬ ∃ (b₀ g₀ h₀ : Point), b₀ ≠ g₀ ∧ b₀ ≠ h₀ ∧ g₀ ≠ h₀ ∧
        b₀.onCircle ABC ∧ g₀.onCircle ABC ∧ h₀.onCircle ABC ∧
        b₀.onCircle DEF ∧ g₀.onCircle DEF ∧ h₀.onCircle DEF :=
  (hABCneDEF (equal_circles p b b ABC DEF ⟨step10.1, step10.2, hbABC, hbDEF, rfl⟩)).elim

end Elements.Book3
