import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_24_step12
  (b c e f g : Point)
  (h_step10 : |(e─g)| > |(e─f)|)
  (h_step11 : |(e─g)| = |(b─c)|)
  : |(b─c)| > |(e─f)| := by
  linarith

end Elements.Book1
