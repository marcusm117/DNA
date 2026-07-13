import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_23_step2 (a c d : Point) (ACD : Line)
    (h_a : a.onLine ACD) (h_d : d.onLine ACD) (h_bet : between a c d) :
    a.onLine ACD ∧ c.onLine ACD ∧ d.onLine ACD := by
  euclid_finish

end Elements.Book3
