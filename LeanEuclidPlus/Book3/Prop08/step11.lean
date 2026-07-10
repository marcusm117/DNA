import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step11 (d e f : Point)
    (hstep8 : |(d─e)| > |(d─f)|) :
    |(d─e)| > |(d─f)| := hstep8

end Elements.Book3
