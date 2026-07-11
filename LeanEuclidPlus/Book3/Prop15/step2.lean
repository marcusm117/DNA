import SystemE
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step2
    (e h k : Point)
    (hassump1 : |(e─h)| < |(e─k)|) :
    |(e─k)| > |(e─h)| := by
  linarith

end Elements.Book3
