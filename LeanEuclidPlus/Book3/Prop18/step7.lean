import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_18_step7 (c d f : Point)
    (habsurd1 : ¬(∠ f:c:d ≠ ∟)) :
    ¬(∠ f:c:d ≠ ∟) := habsurd1

end Elements.Book3
