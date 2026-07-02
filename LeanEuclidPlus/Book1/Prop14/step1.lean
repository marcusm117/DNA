import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_14_step1 (c b e : Point) (h : between c b e) : between c b e := by
  exact h

end Elements.Book1
