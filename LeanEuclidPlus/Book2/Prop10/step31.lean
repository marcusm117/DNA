import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.31: square on EG = double the square on EF. From step30 (|e─g|² = |g─f|² + |f─e|²) and
   step29 (|g─f|² + |f─e|² = 2|e─f|²). Pure linarith. -/
theorem helper_2_10_step31
  (e f g : Point)
  (hstep30 : |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)| + |(f─e)| * |(f─e)|)
  (hstep29 : |(g─f)| * |(g─f)| + |(f─e)| * |(f─e)| = 2 * (|(e─f)| * |(e─f)|)) :
  |(e─g)| * |(e─g)| = 2 * (|(e─f)| * |(e─f)|) := by
  linarith

end Elements.Book2
