import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step21 (a c d e f : Point)
    (hstep20 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)|) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| = |(f─d)| * |(f─d)| + |(e─f)| * |(e─f)| := by
  linarith [hstep20]

end Elements.Book3
