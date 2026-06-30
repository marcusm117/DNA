import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step8_ahb_mag
    (a b e f : Point)
    (hab : a ≠ b)
    (step8_bisect : |(a─b)| = |(a─e)| + |(a─e)|)
    (step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|)
    (step8_eb : |(e─b)| = |(a─e)| + |(a─f)|) :
    |(a─f)| < |(a─b)| := by
  have hab_nn : (0 : ℝ) ≤ |(a─b)| := segment_gte_zero _
  have hab_pos : (0 : ℝ) < |(a─b)| := by
    rcases lt_or_eq_of_le hab_nn with h | h
    · exact h
    · exact (hab (zero_segment_if a b h.symm)).elim
  have hae_nn : (0 : ℝ) ≤ |(a─e)| := segment_gte_zero _
  have heb_nn : (0 : ℝ) ≤ |(e─b)| := segment_gte_zero _
  have haf_nn : (0 : ℝ) ≤ |(a─f)| := segment_gte_zero _
  have hae_pos : (0 : ℝ) < |(a─e)| := by linarith [step8_bisect, hab_pos, hae_nn]
  -- production (|e-b| = |a-e| + |a-f|) + Pythagoras + bisection ⟹ |a-f| < |a-b|
  nlinarith [step8_bisect, step8_pyth, step8_eb, hae_pos, hab_nn, hae_nn, heb_nn, haf_nn]

end Elements.Book2
