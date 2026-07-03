import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_4_step10
  (step9 : ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e)
  : ∠ a:b:c = ∠ d:e:f :=
  step9.1

end Elements.Book1
