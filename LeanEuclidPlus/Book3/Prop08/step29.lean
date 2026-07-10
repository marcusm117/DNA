import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step29
    (d k b0 n : Point)
    (step29_assumption1 : |(d─k)| = |(d─n)|)
    (step29_assumption2 : |(d─k)| = |(d─b0)|) :
    |(d─b0)| = |(d─n)| := by
  linarith

end Elements.Book3
