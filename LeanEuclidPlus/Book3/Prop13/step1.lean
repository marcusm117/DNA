import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_13_step1 (ABDC : Circle) (d b h : Point)
    (hsuppose1 : d ≠ b ∧ h.insideCircle ABDC) :
    d ≠ b ∧ h.insideCircle ABDC := by
  exact hsuppose1

end Elements.Book3
