import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step17 (a b c d e f : Point)
  (hstep16 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|)
  (hstep15 : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|)
  : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| := by
  linarith [hstep16, hstep15]

end Elements.Book3
