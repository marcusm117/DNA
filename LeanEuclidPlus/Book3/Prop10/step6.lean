import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step6
    (step4 : ∃ o : Point, o.isCentre ABC ∧ o.onLine AC)
    : ∃ o : Point, o.isCentre ABC ∧ o.onLine AC :=
  step4

end Elements.Book3
