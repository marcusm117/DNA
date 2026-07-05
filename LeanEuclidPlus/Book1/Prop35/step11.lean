import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_35_step11
  (e a b d g f c : Point)
  (h10 : Triangle.area △ e:a:b = Triangle.area △ d:f:c)
  : Triangle.area △ e:a:b - Triangle.area △ d:g:e = Triangle.area △ d:f:c - Triangle.area △ d:g:e := by
  linarith

end Elements.Book1
