import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_34_step12
  (a b c d : Point) (AB CD AC BD BC : Line)
  (hstep5 : |(a─b)| = |(c─d)|)
  : |(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)| := by
  constructor <;> euclid_finish

end Elements.Book1
