import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step13
    (a b c d : Point)
    (step10 : |(a─d)| > |(b─c)|) :
    |(a─d)| > |(b─c)| :=
  step10

end Elements.Book3
