import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_7_step1 (a c d : Point)
    (h : |(a─c)| = |(a─d)|) : |(c─a)| = |(d─a)| := by
  euclid_finish

end Elements.Book1
