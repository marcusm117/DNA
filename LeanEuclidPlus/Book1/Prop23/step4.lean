import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_23_step4 (c e a g : Point)
    (h_ag : |(a─g)| = |(c─e)|)
    : |(c─e)| = |(a─g)| := by
  euclid_finish

end Elements.Book1
