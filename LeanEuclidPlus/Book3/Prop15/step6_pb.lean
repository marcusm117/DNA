import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagorean for b-side: |b─h|² + |e─h|² = |e─b|² (right angle at h)
theorem helper_3_15_step6_pb
    (b h e : Point) (ABCD : Circle) (BC : Line)
    (h_centre : e.isCentre ABCD) (hb_on : b.onCircle ABCD)
    (hh_BC : h.onLine BC) (hb_BC : b.onLine BC)
    (heh : e ≠ h)
    (h_perp_ehb : ∠ e:h:b = ∟) :
    |(b─h)| * |(b─h)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)| := by
  by_cases hbh : b = h
  · -- degenerate: b = h → |b─h| = 0, |e─h| = |e─b|
    have h0 : |(b─h)| = 0 := zero_segment_onlyif b h hbh
    have heq : |(e─b)| = |(e─h)| := by rw [hbh]
    nlinarith [segment_gte_zero (e─h), h0]
  · euclid_apply (line_from_points e h) as EHl
    euclid_apply (line_from_points e b) as EB
    have htri : formTriangle h e b EHl EB BC := by euclid_finish
    have hp := Elements.Book1.proposition_47 h e b EHl EB BC ⟨htri, h_perp_ehb⟩
    -- hp : |(e─b)| * |(e─b)| = |(e─h)| * |(e─h)| + |(h─b)| * |(h─b)|
    have hsym : |(b─h)| = |(h─b)| := by euclid_finish
    have h_sq_eq : |(b─h)| * |(b─h)| = |(h─b)| * |(h─b)| := by rw [hsym]
    linarith [hp, h_sq_eq]

end Elements.Book3
