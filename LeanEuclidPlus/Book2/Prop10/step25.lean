import SystemE
import Mathlib.Tactic.Ring
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.25: squares on EC + CA = double the square on CA. Substitute step24 (square on EC = square on
   CA), then ring. Pure arithmetic. -/
theorem helper_2_10_step25
  (a c e : Point)
  (hstep24 : |(e─c)| * |(e─c)| = |(c─a)| * |(c─a)|) :
  |(e─c)| * |(e─c)| + |(c─a)| * |(c─a)| = 2 * (|(c─a)| * |(c─a)|) := by
  rw [hstep24]; ring

end Elements.Book2
