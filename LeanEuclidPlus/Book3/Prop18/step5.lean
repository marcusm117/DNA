import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_18_step5 (f c b g : Point)
    (step3 : |(f─c)| > |(f─g)|) (step4 : |(f─c)| = |(f─b)|) :
    |(f─b)| > |(f─g)| := by
  linarith

end Elements.Book3
