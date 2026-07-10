import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step5_p20
    (m e d : Point)
    (step5_assumption1 : |(e─m)| + |(m─d)| > |(e─d)|) :
    |(e─m)| + |(m─d)| > |(e─d)| :=
  step5_assumption1

end Elements.Book3
