import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_30_step5
    (hstep2 : ∠ a:g:k = ∠ g:h:f)
    (hstep3 : ∠ g:h:f = ∠ g:k:d)
    : ∠ a:g:k = ∠ g:k:d := by
  exact hstep2.trans hstep3

end Elements.Book1
