import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_32_step2 (c : Point) (ABCD : Circle) (h_c_circ : c.onCircle ABCD) :
    c.onCircle ABCD := by
  euclid_finish

end Elements.Book3
