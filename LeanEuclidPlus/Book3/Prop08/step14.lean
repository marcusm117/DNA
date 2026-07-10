import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step14 (d g k : Point)
    (hstep13 : |(d─k)| > |(d─g)|) :
    |(d─g)| < |(d─k)| := by
  euclid_finish

end Elements.Book3
