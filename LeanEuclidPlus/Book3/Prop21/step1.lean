import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_21_step1 (f' : Point) (ABCD : Circle) (h : f'.isCentre ABCD) : f'.isCentre ABCD := by
  exact h

end Elements.Book3
