import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_41_step4
    (step2 : Triangle.area △ a:b:c = Triangle.area △ e:b:c)
    (step3 : Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ a:b:c + Triangle.area △ a:b:c) :
    Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ e:b:c + Triangle.area △ e:b:c := by
  linarith

end Elements.Book1
