import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_9_step20
  (a c e : Point)
  (hce : |(c─e)| = |(a─c)|) :
  |(a─c)| * |(a─c)| + |(c─e)| * |(c─e)| = 2 * (|(a─c)| * |(a─c)|) := by
  rw [← hce]; ring

end Elements.Book2
