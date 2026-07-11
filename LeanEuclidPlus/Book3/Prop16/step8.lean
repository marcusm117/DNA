import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_16_step8
    (ABC : Circle) (AE : Line)
    (habsurd1 : ¬AE.intersectsCircle ABC)
    : ¬(AE.intersectsCircle ABC) := by
  exact habsurd1

end Elements.Book3
