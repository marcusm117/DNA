import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step13
    (a b e f : Point)
    (step12 : |(e─a)| = |(e─b)| ∧ |(a─f)| = |(f─b)|)
    : |(a─f)| = |(f─b)| := step12.2

end Elements.Book3
