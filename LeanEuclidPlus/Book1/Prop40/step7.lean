import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_40_step7 (a b c d e f : Point)
    (hstep5 : Triangle.area △ a:b:c = Triangle.area △ f:c:e)
    (hstep6 : Triangle.area △ a:b:c = Triangle.area △ d:c:e) :
    Triangle.area △ d:c:e = Triangle.area △ f:c:e :=
  hstep6.symm.trans hstep5

end Elements.Book1
