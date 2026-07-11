import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- |b─h| = |l─m|: from equal Pythagorean equations + equal radii + equal distances
-- a² = b² ∧ a,b ≥ 0 → a = b via (a-b)(a+b) = 0
set_option systemE.solverTime 30 in
theorem helper_3_15_step6_eq_bh_lm
    (b h l m e : Point)
    (h_pb : |(b─h)| * |(b─h)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)|)
    (h_pm : |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)|)
    (h_rad : |(e─b)| = |(e─m)|)
    (hassump1 : |(e─h)| = |(e─l)|) :
    |(b─h)| = |(l─m)| := by
  have h_rad_sq : |(e─b)| * |(e─b)| = |(e─m)| * |(e─m)| := by rw [h_rad]
  have hassump1_sq : |(e─h)| * |(e─h)| = |(e─l)| * |(e─l)| := by rw [hassump1]
  have h_sq : |(b─h)| * |(b─h)| = |(l─m)| * |(l─m)| := by linarith [h_pb, h_pm, h_rad_sq, hassump1_sq]
  have h_fact : (|(b─h)| - |(l─m)|) * (|(b─h)| + |(l─m)|) = 0 := by nlinarith [h_sq]
  rcases mul_eq_zero.mp h_fact with h1 | h2
  · linarith
  · have := segment_gte_zero (b─h); have := segment_gte_zero (l─m); linarith

end Elements.Book3
