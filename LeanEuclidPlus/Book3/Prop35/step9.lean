import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step9 (a c e g f : Point)
  (hstep8 : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = |(g─c)| * |(g─c)| + |(g─f)| * |(g─f)|)
  : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = |(g─c)| * |(g─c)| + |(g─f)| * |(g─f)| := by
  exact hstep8

end Elements.Book3
