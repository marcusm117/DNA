import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step13
    (a b c e f : Point)
    (hstep11 : |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(e─b)| * |(e─b)|)
    (hstep12 : |(b─a)| * |(b─a)| + |(a─e)| * |(a─e)| = |(e─b)| * |(e─b)|) :
    |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(b─a)| * |(b─a)| + |(a─e)| * |(a─e)| := by
  linarith [hstep11, hstep12]

end Elements.Book2
