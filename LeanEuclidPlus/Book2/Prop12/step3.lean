import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step3
  (c d a b : Point)
  (hstep2 : |(d─c)| * |(d─c)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|))
  : |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_apply (segment_symmetric c d)
  rw [h]; exact hstep2

end Elements.Book2
