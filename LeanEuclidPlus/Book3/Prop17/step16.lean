import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step16 (e b a d f : Point)
    (step14 : ∠ e:d:f = ∠ e:b:a)
    (step15 : ∠ e:d:f = ∟) :
    ∠ e:b:a = ∟ :=
  step14.symm.trans step15

end Elements.Book3
