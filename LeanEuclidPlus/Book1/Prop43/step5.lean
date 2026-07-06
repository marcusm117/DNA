import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step5
    (a b c d : Point)
    (step1 : Triangle.area △ a:b:c = Triangle.area △ a:c:d)
    : Triangle.area △ a:b:c = Triangle.area △ a:d:c := by
  euclid_finish

end Elements.Book1
