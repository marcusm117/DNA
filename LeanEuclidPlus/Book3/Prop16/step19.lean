import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_16_step19
    (a : Point) (ABC : Circle) (AE : Line)
    (habsurd2 : ¬∃ FA, a.onLine FA ∧ FA ≠ AE ∧ ¬FA.intersectsCircle ABC)
    : ¬(∃ (FA : Line), a.onLine FA ∧ FA ≠ AE ∧ ¬FA.intersectsCircle ABC) :=
  habsurd2

end Elements.Book3
