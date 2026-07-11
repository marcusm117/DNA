import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step5
    (a b f : Point) (hstep4 : |(a─f)| = |(f─b)|) :
    |(a─f)| = |(f─b)| := hstep4

end Elements.Book3
