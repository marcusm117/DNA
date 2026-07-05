import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_37_step8 (a b c d e f : Point)
    (h_step5 : Triangle.area △e:b:a + Triangle.area △a:b:c = Triangle.area △d:b:c + Triangle.area △d:c:f)
    (h_step6 : Triangle.area △ a:b:c = Triangle.area △ e:a:b)
    (h_step7 : Triangle.area △ d:b:c = Triangle.area △ f:d:c) :
    Triangle.area △ a:b:c = Triangle.area △ d:b:c := by
  euclid_finish

end Elements.Book1
