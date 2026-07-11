import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step12
    (b c f g m n : Point)
    (step11 : |(m─n)| > |(f─g)|)
    (step12_assumption1 : |(m─n)| = |(b─c)|) :
    |(b─c)| > |(f─g)| := by
  linarith

end Elements.Book3
