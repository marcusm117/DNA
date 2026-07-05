import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_34_step14
  (a b c d : Point) (AB CD AC BD BC : Line)
  (hstep6 : |(a─c)| = |(b─d)|)
  : |(a─c)| = |(d─b)| := by euclid_finish

end Elements.Book1
