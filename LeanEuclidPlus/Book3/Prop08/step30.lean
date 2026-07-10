import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step30
    (d b0 n : Point)
    (step29 : |(d─b0)| = |(d─n)|) :
    |(d─b0)| = |(d─n)| :=
  step29

end Elements.Book3
