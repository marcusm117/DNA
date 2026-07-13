import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step2 (f : Point) (ABCD : Circle)
  (hf : f.isCentre ABCD)
  : f.isCentre ABCD := by
  exact hf

end Elements.Book3
