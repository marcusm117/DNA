import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_39_step6
    (a b c d : Point)
    (hgiven : Triangle.area △ a:b:c = Triangle.area △ d:b:c)
    : Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
  hgiven

end Elements.Book1
