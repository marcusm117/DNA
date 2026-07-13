import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step8 (a c e g f : Point)
  (hstep7 : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| = |(g─c)| * |(g─c)|)
  : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = |(g─c)| * |(g─c)| + |(g─f)| * |(g─f)| := by
  linarith [hstep7]

end Elements.Book3
