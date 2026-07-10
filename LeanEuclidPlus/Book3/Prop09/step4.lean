import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_9_step4
    (a b d : Point)
    (h_da_db : |(d─a)| = |(d─b)|)
    : |(d─a)| = |(d─b)| := h_da_db

end Elements.Book3
