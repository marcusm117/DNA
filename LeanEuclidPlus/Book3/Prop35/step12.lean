import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step12 (a c e f g : Point)
  (hstep7 : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| = |(g─c)| * |(g─c)|)
  (hstep10 : |(f─e)| * |(f─e)| = |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)|)
  (hstep11 : |(f─c)| * |(f─c)| = |(c─g)| * |(c─g)| + |(g─f)| * |(g─f)|)
  : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─c)| * |(f─c)| := by
  euclid_finish

end Elements.Book3
