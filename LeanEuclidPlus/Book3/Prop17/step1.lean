import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_17_step1 (e : Point) (BCD : Circle) (h : e.isCentre BCD) : e.isCentre BCD := by
  exact h

end Elements.Book3
