import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step15 (f d g b : Point)
    (h_step13 : ∠ g:d:b = ∟)
    (h_step14 : ∠ f:d:b = ∟) :
    ∠ f:d:b = ∠ g:d:b :=
  h_step14.trans h_step13.symm

end Elements.Book3
