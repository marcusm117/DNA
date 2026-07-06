import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_48_step4
    (hassump1 : |(d─a)| = |(a─b)|)
    : |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)| := by
  euclid_finish

end Elements.Book1
