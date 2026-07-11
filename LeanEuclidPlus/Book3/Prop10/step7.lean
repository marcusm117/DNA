import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step7
    (p : Point) (AC NO : Line)
    (hpAC : p.onLine AC) (hpNO : p.onLine NO)
    : p.onLine AC ∧ p.onLine NO :=
  ⟨hpAC, hpNO⟩

end Elements.Book3
