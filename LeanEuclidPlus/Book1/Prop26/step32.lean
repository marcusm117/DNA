import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step32
    (hang2 : ∠ b:c:a = ∠ e:f:d) :
    ∠ e:f:d = ∠ b:c:a :=
  hang2.symm

end Elements.Book1
