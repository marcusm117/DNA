import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step10
    (a d b c m e n : Point)
    (step7 : |(a─d)| = |(m─e)| + |(e─n)|)
    (step8 : |(m─e)| + |(e─n)| > |(m─n)|)
    (step9 : |(m─n)| = |(b─c)|) :
    |(a─d)| > |(b─c)| := by
  linarith

end Elements.Book3
