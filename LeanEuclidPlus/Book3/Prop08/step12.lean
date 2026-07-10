import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_8_step12 (d f c : Point)
    (hstep9 : |(d─f)| > |(d─c)|) :
    |(d─f)| > |(d─c)| := hstep9

end Elements.Book3
