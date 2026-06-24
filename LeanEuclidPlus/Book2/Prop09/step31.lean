import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_9_step31
  (a c d e f : Point)
  (hstep29 : |(e─f)| * |(e─f)| = 2 * (|(c─d)| * |(c─d)|))
  (hstep30 : |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|)) :
  |(e─a)| * |(e─a)| + |(e─f)| * |(e─f)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  linarith

end Elements.Book2
