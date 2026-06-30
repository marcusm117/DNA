import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step11
    (a c e f b : Point)
    (hstep9 : |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(e─f)| * |(e─f)|)
    (hstep10 : |(e─f)| = |(e─b)|) :
    |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(e─b)| * |(e─b)| := by
  rw [hstep10] at hstep9
  exact hstep9

end Elements.Book2
