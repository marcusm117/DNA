import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_13_step3 (EBFD : Circle) (h : Point)
    (hcenEBFD : h.isCentre EBFD) :
    h.isCentre EBFD := by
  exact hcenEBFD

end Elements.Book3
