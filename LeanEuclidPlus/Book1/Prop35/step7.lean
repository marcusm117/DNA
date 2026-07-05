import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_35_step7
  (a d e f b c : Point)
  (h5 : |(a─e)| = |(d─f)|)
  (h6 : |(a─b)| = |(d─c)|)
  : |(e─a)| = |(f─d)| ∧ |(a─b)| = |(d─c)| := by
  constructor
  · have hea : |(e─a)| = |(a─e)| := segment_symmetric e a
    have hfd : |(f─d)| = |(d─f)| := segment_symmetric f d
    linarith
  · exact h6

end Elements.Book1
