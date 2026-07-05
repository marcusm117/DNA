import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step8
    (hstep7 : ∠ b:g:c = ∠ e:d:f ∧ ∠ g:c:b = ∠ d:f:e) :
    ∠ g:c:b = ∠ d:f:e :=
  hstep7.2

end Elements.Book1
