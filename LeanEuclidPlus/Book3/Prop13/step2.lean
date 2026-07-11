import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_13_step2 (ABDC : Circle) (g : Point)
    (hcenABDC : g.isCentre ABDC) :
    g.isCentre ABDC := by
  exact hcenABDC

end Elements.Book3
