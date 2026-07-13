import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step16 (a b c e f : Point)
  (hstep14 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|)
  : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by
  exact hstep14

end Elements.Book3
