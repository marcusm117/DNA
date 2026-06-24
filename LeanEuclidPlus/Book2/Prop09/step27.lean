import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_9_step27
  (e f g : Point)
  (hstep25 : |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = 2 * (|(g─f)| * |(g─f)|))
  (hstep26 : |(e─f)| * |(e─f)| = |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)|) :
  |(e─f)| * |(e─f)| = 2 * (|(g─f)| * |(g─f)|) := by
  linarith

end Elements.Book2
