import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step8
    (AB CD : Line)
    (step6 : ∠ b:g:h + ∠ g:h:d < ∟ + ∟)
    (step7 : ∠ b:g:h + ∠ g:h:d < ∟ + ∟ → AB.intersectsLine CD) :
    AB.intersectsLine CD := step7 step6

end Elements.Book1
