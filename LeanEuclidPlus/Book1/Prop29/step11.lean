import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step11
    (step10 : ¬(∠ a:g:h ≠ ∠ g:h:d)) :
    ∠ a:g:h = ∠ g:h:d := Classical.not_not.mp step10

end Elements.Book1
