import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_34_step16
  (a b c d : Point) (AB CD AC BD BC : Line)
  (hstep15 : Triangle.area △ a:b:c = Triangle.area △ b:c:d)
  : Triangle.area △ a:b:c = Triangle.area △ d:c:b := by
  euclid_finish

end Elements.Book1
