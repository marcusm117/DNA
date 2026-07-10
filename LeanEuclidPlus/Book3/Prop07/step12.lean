import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step12
    (hbet_efd : between e f d)
    (step10 : |(g─f)| + |(f─e)| > |(e─d)|)
    : |(g─f)| > |(f─d)| := by
  have hlen : |(e─d)| = |(e─f)| + |(f─d)| := by euclid_finish
  linarith [segment_symmetric f e]

end Elements.Book3
