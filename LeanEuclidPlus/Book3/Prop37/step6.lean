import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step6 (a d c b : Point)
    (h : |(a─d)| * |(d─c)| = |(d─b)| * |(d─b)|) :
    |(a─d)| * |(d─c)| = |(d─b)| * |(d─b)| := h

end Elements.Book3
