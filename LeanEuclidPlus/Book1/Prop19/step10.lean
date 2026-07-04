import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_19_step10
  (hassump1 : |(a─c)| ≠ |(a─b)|)
  : |(a─c)| ≠ |(a─b)| := hassump1

end Elements.Book1
