import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step8
    (a b d : Point)
    (step2 : |(a─d)| = |(a─b)|) :
    |(a─b)| = |(a─d)| := step2.symm

end Elements.Book1
