import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step6
    (a b e f : Point)
    (step5 : ∠ a:f:e = ∟ ∧ ∠ b:f:e = ∟)
    : ∠ a:f:e = ∟ ∧ ∠ b:f:e = ∟ := step5

end Elements.Book3
