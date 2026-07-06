import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step19
    (a b l m : Point) (c₁ c₂ c₃ : Point)
    (f e g : Point)
    (step17 : Triangle.area △ a:b:m + Triangle.area △ a:l:m =
      Triangle.area △ f:g:e + Triangle.area △ f:e:b)
    (step18 : Triangle.area △ f:g:e + Triangle.area △ f:e:b = Triangle.area △ c₁:c₂:c₃)
    : Triangle.area △ a:b:m + Triangle.area △ a:l:m = Triangle.area △ c₁:c₂:c₃ := by
  linarith

end Elements.Book1
