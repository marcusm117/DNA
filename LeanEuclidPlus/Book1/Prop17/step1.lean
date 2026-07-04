import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_17_step1 (b c d : Point) (h : between b c d) : between b c d := by
  assumption

end Elements.Book1
