import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step15
    (step13 : ∠ e:g:b = ∠ g:h:d)
    (step14 : ∠ e:g:b = ∠ g:h:d → ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d) :
    ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d := step14 step13

end Elements.Book1
