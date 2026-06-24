import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_9_step37
  (a c d f : Point)
  (hstep34 : |(a─f)| * |(a─f)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|))
  (hstep35 : |(a─d)| * |(a─d)| + |(d─f)| * |(d─f)| = |(a─f)| * |(a─f)|) :
  |(a─d)| * |(a─d)| + |(d─f)| * |(d─f)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  linarith

end Elements.Book2
