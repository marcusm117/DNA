import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_4_step9 (f e a b : Point)
    (hassump1 : ∠ f:e:a = ∟)
    (hstep8 : ∠ f:e:b = ∟) :
    ∠ f:e:a = ∠ f:e:b :=
  hassump1.trans hstep8.symm

end Elements.Book3
