import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step8 (f a g : Point)
    (step6 : |(f─g)| > |(f─a)| + |(a─g)|)
    (step7 : |(f─g)| < |(f─a)| + |(a─g)|)
    : False := by
  linarith

end Elements.Book3
