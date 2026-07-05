import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step33
    (hstep31 : ∠ b:h:a = ∠ e:f:d)
    (hstep32 : ∠ e:f:d = ∠ b:c:a) :
    ∠ b:h:a = ∠ b:c:a :=
  hstep31.trans hstep32

end Elements.Book1
