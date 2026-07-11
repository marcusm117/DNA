import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Direction-1 arithmetic core (mirror of hge0): with CD a diameter (|CD| = 2R) and
-- |AB| = |CD|, the two Pythagoras identities force |AF| = |FB| = R, hence |FE| = 0.
theorem helper_3_14_gap_cd_diam_fe0
    (a b c d e f : Point)
    (hpyth_a : |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| = |(a─e)| * |(a─e)|)
    (hpyth_b : |(b─f)| * |(b─f)| + |(f─e)| * |(f─e)| = |(a─e)| * |(a─e)|)
    (hchord : |(a─f)| + |(f─b)| = |(a─b)|)
    (hdiam : |(c─d)| = |(a─e)| + |(a─e)|)
    (heq : |(a─b)| = |(c─d)|) :
    |(f─e)| = 0 := by
  have h1 : |(b─f)| = |(f─b)| := segment_symmetric b f
  have hz2_le : |(f─e)| * |(f─e)| ≤ 0 := by
    nlinarith [hpyth_a, hpyth_b, hchord, hdiam, heq, h1,
               segment_gte_zero (a─f), segment_gte_zero (f─b),
               sq_nonneg (|(a─f)| - |(f─b)|)]
  have hz2 : |(f─e)| * |(f─e)| = 0 := le_antisymm hz2_le (mul_self_nonneg _)
  exact mul_self_eq_zero.mp hz2

end Elements.Book3
