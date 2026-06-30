import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step6 (2.13.6): substitute the two Pythagoras results (step4: AB²=BD²+DA²,
-- step5: AC²=AD²+DC²) into step3 to get CB²+BA² = AC² + 2·rect(CB,BD).
-- Segment directions differ across the three hypotheses, so canonicalize the two
-- cross-direction squares and close the (linear-in-squares) system with linarith.
theorem helper_2_13_step6
  (a b c d : Point)
  (hstep3 : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| =
      2 * (|(c─b)| * |(b─d)|) + |(a─d)| * |(a─d)| + |(d─c)| * |(d─c)|)
  (hstep4 : |(a─b)| * |(a─b)| = |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)|)
  (hstep5 : |(a─c)| * |(a─c)| = |(a─d)| * |(a─d)| + |(d─c)| * |(d─c)|)
  : |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| = |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|) := by
  have sba : |(b─a)| * |(b─a)| = |(a─b)| * |(a─b)| := by rw [segment_symmetric b a]
  have sda : |(d─a)| * |(d─a)| = |(a─d)| * |(a─d)| := by rw [segment_symmetric d a]
  linarith [hstep3, hstep4, hstep5, sba, sda]

end Elements.Book2
