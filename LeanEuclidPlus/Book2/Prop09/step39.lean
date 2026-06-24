import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_9_step39
  (a b c d f : Point)
  (hstep37 : |(a─d)| * |(a─d)| + |(d─f)| * |(d─f)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|))
  (hstep38 : |(d─f)| = |(d─b)|) :
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  rw [← hstep38]
  linarith

end Elements.Book2
