import SystemE
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step6 (a g d h : Point)
    (step4 : |(a─g)| > |(g─h)|)
    (step5 : |(a─g)| = |(g─d)|)
    : |(g─d)| > |(g─h)| := by linarith

end Elements.Book3
