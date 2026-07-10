import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step4
    (step2 : |(e─b)| + |(e─f)| > |(b─f)|)
    (step3 : |(e─b)| + |(e─f)| = |(f─a)|)
    : |(f─a)| > |(f─b)| := by
  linarith [segment_symmetric f a, segment_symmetric b f]

end Elements.Book3
