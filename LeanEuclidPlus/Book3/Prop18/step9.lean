import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_18_step9 (c f d : Point)
    (step7 : ¬(∠ f:c:d ≠ ∟)) : ∠ f:c:d = ∟ :=
  Classical.not_not.mp step7

end Elements.Book3
