import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step7
    (a b e f : Point)
    (step6 : ∠ a:f:e = ∟ ∧ ∠ b:f:e = ∟)
    : ∠ a:f:e = ∟ := step6.1

end Elements.Book3
