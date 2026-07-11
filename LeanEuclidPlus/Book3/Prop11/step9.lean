import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step9 (a f g : Point)
    (step8 : ¬¬between f g a)
    : between f g a := by
  by_contra h
  exact step8 h

end Elements.Book3
