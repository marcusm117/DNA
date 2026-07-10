import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step24
    (hassump1 : |(f─k)| = |(f─g)|)
    (hassump2 : |(f─h)| = |(f─g)|)
    : |(f─k)| = |(f─h)| := by
  linarith

end Elements.Book3
