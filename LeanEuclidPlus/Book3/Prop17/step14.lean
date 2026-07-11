import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step14 (e d f b a : Point)
    (step13 : ∠ e:d:f = ∠ e:b:a ∧ ∠ e:f:d = ∠ e:a:b) :
    ∠ e:d:f = ∠ e:b:a :=
  step13.1

end Elements.Book3
