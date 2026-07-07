import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_step7 (e c f g : Point)
    (step4 : |(e─c)| = |(e─f)|) (step5 : |(e─c)| = |(e─g)|)
    : |(e─f)| = |(e─g)| := by
  linarith

end Elements.Book3
