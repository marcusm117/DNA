import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step19 (a b c d e : Point)
  (hstep18 : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)|)
  : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)| := by
  exact hstep18

end Elements.Book3
