import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_9_step29
  (c d e f g : Point)
  (hstep27 : |(e─f)| * |(e─f)| = 2 * (|(g─f)| * |(g─f)|))
  (hstep28 : |(g─f)| = |(c─d)|) :
  |(e─f)| * |(e─f)| = 2 * (|(c─d)| * |(c─d)|) := by
  rw [← hstep28]
  linarith

end Elements.Book2
