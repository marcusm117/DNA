import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_18_hcdDE (c d : Point) (DE : Line)
    (h_con : c.onLine DE) (h_don : d.onLine DE) (h_ne : d ≠ c) :
    distinctPointsOnLine c d DE := by
  euclid_finish

end Elements.Book3
