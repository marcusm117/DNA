import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_34_step5
  (a b c d : Point) (AB CD AC BD BC : Line)
  (hstep4 : |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b)
  : |(a─b)| = |(c─d)| := hstep4.1

end Elements.Book1
