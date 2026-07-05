import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step9
    (AB CD : Line)
    (step8 : AB.intersectsLine CD)
    (step9_assumption1 : ¬(AB.intersectsLine CD)) :
    False := step9_assumption1 step8

end Elements.Book1
