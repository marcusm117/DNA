import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step30 (a b c d e : Point)
    (hstep29 : |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)|) :
    |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)| := by
  linarith [hstep29]

end Elements.Book3
