import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_35_step13
  (a b c d e f g : Point)
  (h12 : Triangle.area △ a:b:d + Triangle.area △ b:g:d = Triangle.area △ e:g:c + Triangle.area △ e:c:f)
  : Triangle.area △ a:b:d + Triangle.area △ b:g:d + Triangle.area △ g:b:c =
    Triangle.area △ e:g:c + Triangle.area △ e:c:f + Triangle.area △ g:b:c := by
  linarith

end Elements.Book1
