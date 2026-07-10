import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_8_step10 (d a e : Point)
    (hstep5 : |(d─a)| > |(d─e)|) :
    |(d─a)| > |(d─e)| := hstep5

end Elements.Book3
