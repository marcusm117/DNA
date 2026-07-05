import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_34_step13
  (a b c d : Point) (AB CD AC BD BC : Line)
  (hstep1 : ∠ a:b:c = ∠ b:c:d)
  : ∠ a:b:c = ∠ b:c:d := hstep1

end Elements.Book1
