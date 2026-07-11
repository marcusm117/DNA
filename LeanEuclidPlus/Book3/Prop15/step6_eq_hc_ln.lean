import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- |h─c| = |l─n|: from equal Pythagorean equations + equal radii + equal distances
theorem helper_3_15_step6_eq_hc_ln
    (h c l n e b m : Point)
    (h_pc : |(h─c)| * |(h─c)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)|)
    (h_pn : |(l─n)| * |(l─n)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)|)
    (h_rad : |(e─b)| = |(e─m)|)
    (hassump1 : |(e─h)| = |(e─l)|) :
    |(h─c)| = |(l─n)| := by
  have h_rad_sq : |(e─b)| * |(e─b)| = |(e─m)| * |(e─m)| := by rw [h_rad]
  have hassump1_sq : |(e─h)| * |(e─h)| = |(e─l)| * |(e─l)| := by rw [hassump1]
  have h_sq : |(h─c)| * |(h─c)| = |(l─n)| * |(l─n)| := by linarith [h_pc, h_pn, h_rad_sq, hassump1_sq]
  have h_fact : (|(h─c)| - |(l─n)|) * (|(h─c)| + |(l─n)|) = 0 := by nlinarith [h_sq]
  rcases mul_eq_zero.mp h_fact with h1 | h2
  · linarith
  · have := segment_gte_zero (h─c); have := segment_gte_zero (l─n); linarith

end Elements.Book3
