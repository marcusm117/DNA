import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step8 (a f g : Point)
    (habsurd1 : ¬¬between f g a)
    : ¬(¬(between f g a)) := habsurd1

end Elements.Book3
