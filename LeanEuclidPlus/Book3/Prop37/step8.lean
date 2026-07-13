import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step8 (d e b : Point)
    (h7 : |(d─e)| * |(d─e)| = |(d─b)| * |(d─b)|) : |(d─e)| = |(d─b)| := by
  have h1 : (0:ℝ) ≤ |(d─e)| := segment_gte_zero _
  have h2 : (0:ℝ) ≤ |(d─b)| := segment_gte_zero _
  nlinarith [h7, h1, h2, sq_nonneg (|(d─e)| - |(d─b)|), sq_nonneg (|(d─e)| + |(d─b)|)]

end Elements.Book3
