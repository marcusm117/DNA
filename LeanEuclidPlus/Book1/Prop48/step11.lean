import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_48_step11
    (hassump1 : |(d─a)| = |(a─b)|)
    (hassump2 : distinctPointsOnLine a c AC)
    : |(d─a)| = |(b─a)| ∧ |(a─c)| = |(a─c)| := by
  constructor
  · euclid_finish
  · rfl

end Elements.Book1
