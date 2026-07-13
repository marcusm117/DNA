import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_hfene (f e : Point) (ABC : Circle)
    (h1 : f.isCentre ABC) (h2 : e.onCircle ABC) : f ≠ e := by euclid_finish

end Elements.Book3
