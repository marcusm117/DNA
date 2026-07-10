import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step14
    (step12 : |(g─f)| > |(f─d)|)
    : |(f─g)| > |(f─d)| := by
  linarith [segment_symmetric g f]

end Elements.Book3
