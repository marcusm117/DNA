import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step18 (a b c d e f : Point)
  (hstep17 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)|)
  : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)| := by
  linarith [hstep17]

end Elements.Book3
