import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.33: square on EG = double the square on CD. From step31 (|e─g|² = 2|e─f|²) and step32
   (|e─f| = |c─d|, squared). Pure linarith over the locked equations. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step33
  (c d e f g : Point)
  (hstep31 : |(e─g)| * |(e─g)| = 2 * (|(e─f)| * |(e─f)|))
  (hstep32 : |(e─f)| = |(c─d)|) :
  |(e─g)| * |(e─g)| = 2 * (|(c─d)| * |(c─d)|) := by
  have hef2 : |(e─f)| * |(e─f)| = |(c─d)| * |(c─d)| := by rw [hstep32]
  linarith

end Elements.Book2
