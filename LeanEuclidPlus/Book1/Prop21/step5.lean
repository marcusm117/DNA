import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_21_step5 (b c d e : Point)
    (hassump1 : |(c─e)| + |(e─d)| > |(c─d)|) :
    |(c─e)| + |(e─d)| + |(d─b)| > |(c─d)| + |(d─b)| := by
  linarith

end Elements.Book1
