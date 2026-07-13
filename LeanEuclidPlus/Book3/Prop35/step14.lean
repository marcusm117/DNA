import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step14 (a b c e f : Point)
  (hstep12 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─c)| * |(f─c)|)
  (hstep13 : |(f─c)| = |(f─b)|)
  : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by
  euclid_finish

end Elements.Book3
