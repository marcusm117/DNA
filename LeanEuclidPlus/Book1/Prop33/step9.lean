import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_33_step9
  (a b c d : Point)
  (step4 : |(a─c)| = |(b─d)|)
  : |(a─c)| = |(b─d)| := step4

end Elements.Book1
