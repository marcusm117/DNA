import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.35: squares on AE + EG = double the (squares on AC + CD). From step34 (square on EA = 2·square on
   AC) and step33 (square on EG = 2·square on CD); segment symmetry reconciles |a─e|/|e─a|. Pure linarith. -/
theorem helper_2_10_step35
  (a c d e g : Point)
  (hstep34 : |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|))
  (hstep33 : |(e─g)| * |(e─g)| = 2 * (|(c─d)| * |(c─d)|)) :
  |(a─e)| * |(a─e)| + |(e─g)| * |(e─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  have hae2 : |(a─e)| * |(a─e)| = |(e─a)| * |(e─a)| := by rw [segment_symmetric a e]
  linarith

end Elements.Book2
