import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_9_step34
  (a c d e f : Point)
  (hstep31 : |(e─a)| * |(e─a)| + |(e─f)| * |(e─f)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|))
  (hstep32 : |(a─f)| * |(a─f)| = |(e─a)| * |(e─a)| + |(e─f)| * |(e─f)|) :
  |(a─f)| * |(a─f)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  linarith

end Elements.Book2
