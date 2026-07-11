import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step3 (a e : Point) (AFG : Circle)
    (hc : e.isCentre AFG) (ha : a.onCircle AFG) : e.isCentre AFG ∧ a.onCircle AFG := by
  exact ⟨hc, ha⟩

end Elements.Book3
