import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.29: squares on GF + FE = double the square on EF. From step28 (square on FG = square on FE);
   segment symmetry reconciles the |g─f|/|f─g| and |f─e|/|e─f| orientations. Pure linarith. -/
theorem helper_2_10_step29
  (e f g : Point)
  (hstep28 : |(f─g)| * |(f─g)| = |(f─e)| * |(f─e)|) :
  |(g─f)| * |(g─f)| + |(f─e)| * |(f─e)| = 2 * (|(e─f)| * |(e─f)|) := by
  have hgf : |(g─f)| * |(g─f)| = |(f─g)| * |(f─g)| := by rw [segment_symmetric g f]
  have hfe : |(f─e)| * |(f─e)| = |(e─f)| * |(e─f)| := by rw [segment_symmetric f e]
  linarith

end Elements.Book2
