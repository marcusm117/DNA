import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_24_step11
  (b c e g : Point)
  (h_step6 : |(b─c)| = |(e─g)|)
  : |(e─g)| = |(b─c)| :=
  h_step6.symm

end Elements.Book1
