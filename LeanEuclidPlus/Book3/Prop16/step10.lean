import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_step10
    (a : Point) (ABC : Circle) (AE : Line)
    (left_1 : a.onCircle ABC)
    (left_5 : a.onLine AE)
    (step8 : ¬AE.intersectsCircle ABC)
    : (∃ p : Point, p.onLine AE ∧ p.onCircle ABC) ∧ ¬ AE.intersectsCircle ABC :=
  ⟨⟨a, left_5, left_1⟩, step8⟩

end Elements.Book3
