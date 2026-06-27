import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step28 (b c d : Point)
    (h_bd : |(b─d)| = |(c─b)|) :
    |(b─d)| = |(b─c)| := by
  euclid_finish

end Elements.Book2
