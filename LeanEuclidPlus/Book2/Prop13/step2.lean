import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step2 (2.13.2): "Let the square on DA be added to both." Pure algebra: step1 + |(d─a)|² to both sides.
theorem helper_2_13_step2
  (c b d a : Point)
  (hstep1 : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| = 2 * (|(c─b)| * |(b─d)|) + |(d─c)| * |(d─c)|)
  : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| =
      2 * (|(c─b)| * |(b─d)|) + |(d─c)| * |(d─c)| + |(d─a)| * |(d─a)| := by
  rw [hstep1]

end Elements.Book2
