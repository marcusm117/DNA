import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_19_step1 (f : Point) (ABC : Circle) (h : f.isCentre ABC) : f.isCentre ABC := h

end Elements.Book3
