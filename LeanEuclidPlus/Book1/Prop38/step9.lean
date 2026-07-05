import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_38_step9
    (a b c d e f g h : Point)
    (hstep5 : Triangle.area △ g:b:c + Triangle.area △ g:c:a =
              Triangle.area △ d:e:f + Triangle.area △ d:f:h)
    (hstep6 : Triangle.area △ a:b:c + Triangle.area △ a:b:c =
              Triangle.area △ g:b:c + Triangle.area △ g:c:a)
    (hstep7 : Triangle.area △ f:e:d + Triangle.area △ f:e:d =
              Triangle.area △ d:e:f + Triangle.area △ d:f:h)
    (hstep8 : (Triangle.area △ a:b:c + Triangle.area △ a:b:c =
                Triangle.area △ g:b:c + Triangle.area △ g:c:a ∧
               Triangle.area △ f:e:d + Triangle.area △ f:e:d =
                Triangle.area △ d:e:f + Triangle.area △ d:f:h ∧
               Triangle.area △ g:b:c + Triangle.area △ g:c:a =
                Triangle.area △ d:e:f + Triangle.area △ d:f:h) →
              Triangle.area △ a:b:c = Triangle.area △ f:e:d)
    : Triangle.area △ a:b:c = Triangle.area △ d:e:f := by
  linarith [hstep8 ⟨hstep6, hstep7, hstep5⟩, area_symm_1 f e d, area_symm_2 d f e]

end Elements.Book1
