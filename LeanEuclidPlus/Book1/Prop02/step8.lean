import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_2_step8 (d a b : Point)
    (h1 : |(d─a)| = |(a─b)|) (h2 : |(d─b)| = |(a─b)|) :
    |(d─a)| = |(d─b)| := by
  euclid_finish

end Elements.Book1
