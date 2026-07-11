import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step7
    (a d e m n : Point)
    (hbetw_aed : between a e d)
    (hassump1 : |(a─e)| = |(m─e)| ∧ |(e─d)| = |(e─n)|) :
    |(a─d)| = |(m─e)| + |(e─n)| := by
  have h_sum := between_if a e d hbetw_aed
  linarith [hassump1.1, hassump1.2, h_sum]

end Elements.Book3
