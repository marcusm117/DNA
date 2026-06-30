import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step23
    (a b d f g h k : Point)
    (hstep20 : Triangle.area △ f:g:h + Triangle.area △ f:a:h = Triangle.area △ h:b:d + Triangle.area △ h:k:d)
    (hstep21 : Triangle.area △ h:b:d + Triangle.area △ h:k:d = |(a─b)| * |(b─h)|)
    (hstep22 : Triangle.area △ f:g:h + Triangle.area △ f:a:h = |(a─h)| * |(a─h)|) :
    |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| := by
  linarith [hstep20, hstep21, hstep22]

end Elements.Book2
