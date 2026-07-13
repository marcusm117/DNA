import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step7 (a c d e b : Point)
    (h5 : |(a─d)| * |(d─c)| = |(d─e)| * |(d─e)|)
    (h6 : |(a─d)| * |(d─c)| = |(d─b)| * |(d─b)|) :
    |(d─e)| * |(d─e)| = |(d─b)| * |(d─b)| := h5.symm.trans h6

end Elements.Book3
