import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step9
    (b c m n : Point)
    (step6 : |(b─c)| = |(m─n)|) :
    |(m─n)| = |(b─c)| := step6.symm

end Elements.Book3
