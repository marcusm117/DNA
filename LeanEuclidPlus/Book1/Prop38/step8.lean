import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_38_step8
    (a b c d e f g h : Point)
    : (Triangle.area △ a:b:c + Triangle.area △ a:b:c = Triangle.area △ g:b:c + Triangle.area △ g:c:a ∧
       Triangle.area △ f:e:d + Triangle.area △ f:e:d = Triangle.area △ d:e:f + Triangle.area △ d:f:h ∧
       Triangle.area △ g:b:c + Triangle.area △ g:c:a = Triangle.area △ d:e:f + Triangle.area △ d:f:h) →
      Triangle.area △ a:b:c = Triangle.area △ f:e:d := by
  intro ⟨h6, h7, h5⟩
  linarith

end Elements.Book1
