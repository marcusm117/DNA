import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step10
    (ABC DEF : Circle) (p : Point)
    (step8 : p.isCentre ABC) (step9 : p.isCentre DEF)
    : p.isCentre ABC ∧ p.isCentre DEF :=
  ⟨step8, step9⟩

end Elements.Book3
