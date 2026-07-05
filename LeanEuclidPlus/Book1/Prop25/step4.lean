import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_25_step4
    (h_gt : |(b─c)| > |(e─f)|)
    (h_eq : |(b─c)| = |(e─f)|) :
    False := by
  linarith

end Elements.Book1
