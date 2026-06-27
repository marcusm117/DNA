import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.37: square on AG = double the (squares on AC + CD). From step36 (|a─g|² = |a─e|² + |e─g|²) and
   step35 (|a─e|² + |e─g|² = 2(|a─c|² + |c─d|²)). Pure linarith. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step37
  (a c d e g : Point)
  (hstep36 : |(a─g)| * |(a─g)| = |(a─e)| * |(a─e)| + |(e─g)| * |(e─g)|)
  (hstep35 : |(a─e)| * |(a─e)| + |(e─g)| * |(e─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) :
  |(a─g)| * |(a─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  linarith

end Elements.Book2
