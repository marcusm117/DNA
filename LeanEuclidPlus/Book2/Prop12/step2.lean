import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step2
  (d c a b : Point)
  (hstep1 : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|))
  : |(d─c)| * |(d─c)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|) := by
  rw [hstep1]; ring

end Elements.Book2
