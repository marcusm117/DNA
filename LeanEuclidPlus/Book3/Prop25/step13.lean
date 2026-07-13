import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step13 (a b e : Point)
    (hstep9 : |(e─b)| = |(e─a)|) :
    |(a─e)| = |(b─e)| := by
  euclid_finish

end Elements.Book3
