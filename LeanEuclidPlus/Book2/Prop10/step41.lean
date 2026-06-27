import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.41 (conclusion): squares on AD + DB = double the (squares on AC + CD). From step39 (|a─d|² +
   |d─g|² = 2(|a─c|² + |c─d|²)) and step40 (|d─g| = |d─b|, squared). Pure linarith. -/
theorem helper_2_10_step41
  (a b c d g : Point)
  (hstep39 : |(a─d)| * |(a─d)| + |(d─g)| * |(d─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|))
  (hstep40 : |(d─g)| = |(d─b)|) :
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  have hdg2 : |(d─g)| * |(d─g)| = |(d─b)| * |(d─b)| := by rw [hstep40]
  linarith

end Elements.Book2
