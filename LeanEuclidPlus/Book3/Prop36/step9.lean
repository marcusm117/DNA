import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step9 (a b c d f : Point)
    (hstep7 : |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─d)| * |(f─d)|)
    (hstep8 : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)|) :
    |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  linarith [hstep7, hstep8]

end Elements.Book3
