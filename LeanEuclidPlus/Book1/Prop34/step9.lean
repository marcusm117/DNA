import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_34_step9
  (a b c d : Point) (AB CD AC BD BC : Line)
  (hstep4 : |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b)
  : ∠ b:a:c = ∠ c:d:b := hstep4.2.2

end Elements.Book1
