import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step2 (a e : Point) (AE : Line)
    (ha : a.onLine AE) (he : e.onLine AE) (hane : a ≠ e) : distinctPointsOnLine a e AE := by
  exact ⟨ha, he, hane⟩

end Elements.Book3
