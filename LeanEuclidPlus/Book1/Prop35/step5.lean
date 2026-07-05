import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_35_step5
  (a d e f : Point)
  (hbet1 : between a d e)
  (hbet2 : between d e f)
  (h3 : |(a─d)| = |(e─f)|)
  : |(a─e)| = |(d─f)| := by
  have h1 : |(a─d)| + |(d─e)| = |(a─e)| := between_if a d e hbet1
  have h2 : |(d─e)| + |(e─f)| = |(d─f)| := between_if d e f hbet2
  linarith

end Elements.Book1
