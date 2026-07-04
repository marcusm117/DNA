import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_19_step11
    (h_ne : |(a─c)| ≠ |(a─b)|)
    (h_nlt : ¬(|(a─c)| < |(a─b)|)) :
    |(a─c)| > |(a─b)| := by
  rcases lt_or_gt_of_ne h_ne with h | h
  · exact absurd h h_nlt
  · exact h

end Elements.Book1
