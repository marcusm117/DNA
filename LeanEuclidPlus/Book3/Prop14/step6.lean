import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step6
    (a b f : Point) (hafb : between a f b) (hstep5 : |(a─f)| = |(f─b)|) :
    |(a─b)| = |(a─f)| + |(a─f)| := by
  have hsum : |(a─f)| + |(f─b)| = |(a─b)| := between_if a f b hafb
  linarith

end Elements.Book3
