import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_9_step23
  (a c e : Point)
  (hstep20 : |(a─c)| * |(a─c)| + |(c─e)| * |(c─e)| = 2 * (|(a─c)| * |(a─c)|))
  (hstep21 : |(e─a)| * |(e─a)| = |(a─c)| * |(a─c)| + |(c─e)| * |(c─e)|) :
  |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|) := by
  linarith

end Elements.Book2
