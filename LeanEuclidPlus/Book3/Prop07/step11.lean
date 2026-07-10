import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step11
    (step10 : |(g─f)| + |(f─e)| > |(e─d)|)
    : |(g─f)| > |(e─d)| - |(e─f)| := by
  linarith [segment_symmetric f e]

end Elements.Book3
