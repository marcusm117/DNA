import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Direction-1 arithmetic core: with AB a diameter (|AB| = 2R) and |AB| = |CD|,
-- the two Pythagoras identities force |CG| = |GD| = R, hence the distance |GE| = 0.
theorem helper_3_14_hge0
    (a b c d e g : Point)
    (hpyth_c : |(c─g)| * |(c─g)| + |(g─e)| * |(g─e)| = |(a─e)| * |(a─e)|)
    (hpyth_d : |(d─g)| * |(d─g)| + |(g─e)| * |(g─e)| = |(a─e)| * |(a─e)|)
    (hchord : |(c─g)| + |(g─d)| = |(c─d)|)
    (hdiam : |(a─b)| = |(a─e)| + |(a─e)|)
    (heq : |(a─b)| = |(c─d)|) :
    |(g─e)| = 0 := by
  have h1 : |(d─g)| = |(g─d)| := segment_symmetric d g
  have hz2_le : |(g─e)| * |(g─e)| ≤ 0 := by
    nlinarith [hpyth_c, hpyth_d, hchord, hdiam, heq, h1,
               segment_gte_zero (c─g), segment_gte_zero (g─d),
               sq_nonneg (|(c─g)| - |(g─d)|)]
  have hz2 : |(g─e)| * |(g─e)| = 0 := le_antisymm hz2_le (mul_self_nonneg _)
  exact mul_self_eq_zero.mp hz2

end Elements.Book3
