import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_20_step7 (a c d : Point) (hassump1 : |(d─a)| = |(a─c)|) :
    |(d─a)| = |(a─c)| :=
  hassump1

end Elements.Book1
