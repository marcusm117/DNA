import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- h is inside ABCD: foot of perp from centre is inside the circle (non-diameter chord)
theorem helper_3_15_step6_hins
    (b h e : Point) (ABCD : Circle)
    (h_centre : e.isCentre ABCD) (hb_on : b.onCircle ABCD)
    (heh : e ≠ h)
    (h_perp_ehb : ∠ e:h:b = ∟)
    (h_pb : |(b─h)| * |(b─h)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)|) :
    h.insideCircle ABCD := by
  -- h ≠ b: if h = b then ∠e:b:b = ∟ which is degenerate (SMT refutes it)
  have h_hb_ne : h ≠ b := by
    intro heq
    subst heq
    exact absurd h_perp_ehb (by euclid_finish)
  -- |h─b| > 0
  have h0 : |(h─b)| ≠ 0 := fun heq => h_hb_ne (zero_segment_if h b heq)
  have h_hb_pos : 0 < |(h─b)| * |(h─b)| := by
    have hpos : 0 < |(h─b)| := lt_of_le_of_ne (segment_gte_zero _) (Ne.symm h0)
    exact mul_pos hpos hpos
  -- |b─h|² = |h─b|² (segment symmetry)
  have h_sym : |(b─h)| = |(h─b)| := by euclid_finish
  have h_sq_eq : |(b─h)| * |(b─h)| = |(h─b)| * |(h─b)| := by rw [h_sym]
  -- |e─h|² < |e─b|² (from Pythagorean: A² = B² + C², C > 0 → B² < A²)
  have h_sq_lt : |(e─h)| * |(e─h)| < |(e─b)| * |(e─b)| := by
    linarith [h_pb, h_sq_eq, h_hb_pos]
  -- |e─h| < |e─b| (from squared inequality + non-negativity)
  have h_lt : |(e─h)| < |(e─b)| := by
    nlinarith [h_sq_lt, segment_gte_zero (e─h), segment_gte_zero (e─b)]
  exact point_in_circle_if e b h ABCD ⟨h_centre, hb_on, h_lt⟩

end Elements.Book3
