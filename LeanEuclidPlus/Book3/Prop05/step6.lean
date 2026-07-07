import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_step6 (e c f : Point)
    (step4 : |(e─c)| = |(e─f)|)
    : |(e─c)| = |(e─f)| := by
  exact step4

end Elements.Book3
