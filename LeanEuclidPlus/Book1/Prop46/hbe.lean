import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_hbe
    (a b d e : Point)
    (step2 : |(a─d)| = |(a─b)|)
    (step7 : |(a─d)| = |(b─e)|) :
    |(b─e)| = |(a─b)| := by
  euclid_finish

end Elements.Book1
