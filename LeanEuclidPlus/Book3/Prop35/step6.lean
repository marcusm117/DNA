import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step6 (a c g : Point)
  (hstep5 : |(a─g)| = |(g─c)|)
  : |(a─g)| = |(g─c)| := by
  exact hstep5

end Elements.Book3
