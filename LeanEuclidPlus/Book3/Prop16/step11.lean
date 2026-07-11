import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_16_step11
    (step10 : (∃ p : Point, p.onLine AE ∧ p.onCircle ABC) ∧ ¬ AE.intersectsCircle ABC)
    : (∃ p : Point, p.onLine AE ∧ p.onCircle ABC) ∧ ¬ AE.intersectsCircle ABC :=
  step10

end Elements.Book3
