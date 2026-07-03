import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_7_step2 (c d b : Point) (h : |(c─b)| = |(d─b)|) : |(c─b)| = |(d─b)| := by
  exact h

end Elements.Book1
