import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_35_step3
  (a d e f b c : Point)
  (h1 : |(a─d)| = |(b─c)|)
  (h2 : |(e─f)| = |(b─c)|)
  : |(a─d)| = |(e─f)| := by
  linarith

end Elements.Book1
