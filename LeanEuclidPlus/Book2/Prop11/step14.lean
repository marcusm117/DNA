import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step14
    (a b c e f : Point)
    (hstep13 : |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(b─a)| * |(b─a)| + |(a─e)| * |(a─e)|) :
    |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)| := by
  have hba : |(b─a)| = |(a─b)| := segment_symmetric b a
  rw [hba] at hstep13
  linarith [hstep13]

end Elements.Book2
