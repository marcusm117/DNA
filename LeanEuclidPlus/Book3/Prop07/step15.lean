import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step15
    (step7 : |(b─f)| > |(c─f)|)
    : |(f─b)| > |(f─c)| := by
  linarith [segment_symmetric b f, segment_symmetric c f]

end Elements.Book3
