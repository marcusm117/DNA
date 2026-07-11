import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step1
    (ABC DEF : Circle) (b g h : Point)
    (hbg : b ≠ g) (hbh : b ≠ h) (hgh : g ≠ h)
    (hbABC : b.onCircle ABC) (hgABC : g.onCircle ABC) (hhABC : h.onCircle ABC)
    (hbDEF : b.onCircle DEF) (hgDEF : g.onCircle DEF) (hhDEF : h.onCircle DEF)
    : b ≠ g ∧ b ≠ h ∧ g ≠ h ∧ b.onCircle ABC ∧ g.onCircle ABC ∧ h.onCircle ABC ∧ b.onCircle DEF ∧ g.onCircle DEF ∧ h.onCircle DEF := by
  exact ⟨hbg, hbh, hgh, hbABC, hgABC, hhABC, hbDEF, hgDEF, hhDEF⟩

end Elements.Book3
