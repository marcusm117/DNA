import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_9_step19
  (a c e : Point)
  (hce : |(c─e)| = |(a─c)|) :
  |(a─c)| * |(a─c)| = |(c─e)| * |(c─e)| := by
  rw [← hce]

end Elements.Book2
