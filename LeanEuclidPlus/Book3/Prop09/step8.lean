import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_9_step8
    (a b d e : Point)
    (hstep6 : ∠ a:e:d = ∟ ∧ ∠ b:e:d = ∟)
    : ∠ a:e:d = ∟ := hstep6.1

end Elements.Book3
