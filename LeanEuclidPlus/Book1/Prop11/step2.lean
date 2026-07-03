import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_11_step2 (c d e : Point) (h : |(c─e)| = |(c─d)|) : |(c─e)| = |(c─d)| := by
  assumption

end Elements.Book1
