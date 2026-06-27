import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.39: squares on AD + DG = double the (squares on AC + CD). From step38 (|a─d|² + |d─g|² = |a─g|²)
   and step37 (|a─g|² = 2(|a─c|² + |c─d|²)). Pure linarith. -/
theorem helper_2_10_step39
  (a c d g : Point)
  (hstep38 : |(a─d)| * |(a─d)| + |(d─g)| * |(d─g)| = |(a─g)| * |(a─g)|)
  (hstep37 : |(a─g)| * |(a─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) :
  |(a─d)| * |(a─d)| + |(d─g)| * |(d─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  linarith

end Elements.Book2
