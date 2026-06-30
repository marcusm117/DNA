import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step18
    (a b c d f g k : Point)
    (hstep16 : Triangle.area △ f:g:k + Triangle.area △ f:c:k = |(c─f)| * |(f─a)|)
    (hstep15 : |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)|)
    (hstep17 : Triangle.area △ a:b:d + Triangle.area △ a:c:d = |(a─b)| * |(a─b)|) :
    Triangle.area △ f:g:k + Triangle.area △ f:c:k = Triangle.area △ a:b:d + Triangle.area △ a:c:d := by
  linarith [hstep16, hstep15, hstep17]

end Elements.Book2
