import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_37_step9 (a b c d : Point)
    (h_step8 : Triangle.area △ a:b:c = Triangle.area △ d:b:c) :
    Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
  h_step8

end Elements.Book1
