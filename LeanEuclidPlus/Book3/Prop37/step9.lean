import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step9 (f e b : Point) (ABC : Circle)
    (h_cen : f.isCentre ABC) (h_e : e.onCircle ABC) (h_b : b.onCircle ABC) :
    |(f─e)| = |(f─b)| := by euclid_finish

end Elements.Book3
