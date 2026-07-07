import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step13 (a d g b : Point)
    (h_step12 : ∠ a:d:g = ∟ ∧ ∠ g:d:b = ∟) :
    ∠ g:d:b = ∟ :=
  h_step12.2

end Elements.Book3
