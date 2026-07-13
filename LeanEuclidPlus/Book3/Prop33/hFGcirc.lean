import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- FG passes through the centre g of α, so it crosses the circle.
theorem helper_3_33_hFGcirc
    (g : Point) (FG : Line) (α : Circle)
    (hgcen : g.isCentre α) (hgFG : g.onLine FG) :
    FG.intersectsCircle α := by
  euclid_finish

end Elements.Book3
