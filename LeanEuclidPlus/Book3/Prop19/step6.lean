import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_19_step6 (a c f e : Point)
    (step3 : ∠ f:c:e = ∟) (step5 : ∠ a:c:e = ∟) : ∠ f:c:e = ∠ a:c:e :=
  step3.trans step5.symm

end Elements.Book3
