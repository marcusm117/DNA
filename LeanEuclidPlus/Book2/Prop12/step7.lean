import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step7
  (a b c d : Point)
  (hstep6 : |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|))
  : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_apply (segment_symmetric c b)
  euclid_apply (segment_symmetric a b)
  euclid_apply (segment_symmetric a c)
  rw [h, h_1] at hstep6
  rw [hstep6, h_2]; ring

end Elements.Book2
