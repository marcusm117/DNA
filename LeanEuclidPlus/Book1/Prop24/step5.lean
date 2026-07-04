import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_24_step5
  (h_step1 : ∠ e:d:g = ∠ b:a:c)
  : ∠ b:a:c = ∠ e:d:g := h_step1.symm

end Elements.Book1
