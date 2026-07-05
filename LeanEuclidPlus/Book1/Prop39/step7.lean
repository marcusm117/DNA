import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_39_step7
    (a b c d e : Point)
    (step5 : Triangle.area △ a:b:c = Triangle.area △ e:b:c)
    (step6 : Triangle.area △ a:b:c = Triangle.area △ d:b:c)
    : Triangle.area △ d:b:c = Triangle.area △ e:b:c :=
  step6.symm.trans step5

end Elements.Book1
