import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step7 (e m f d : Point) (hang : ∠ e:m:d > ∠ f:m:d) :
    ∠ e:m:d > ∠ f:m:d := hang

end Elements.Book3
