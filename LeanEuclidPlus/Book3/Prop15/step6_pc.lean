import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagorean for c-side: |h─c|² + |e─h|² = |e─b|²
-- ∠e:h:c = ∟ from ∠e:h:b = ∟ + collinearity of b,h,c (h≠b, h≠c, EH line provided).
set_option systemE.solverTime 30 in
theorem helper_3_15_step6_pc
    (b c h e : Point) (ABCD : Circle) (BC EH : Line)
    (h_centre : e.isCentre ABCD)
    (hb_on : b.onCircle ABCD) (hc_on : c.onCircle ABCD)
    (hh_BC : h.onLine BC) (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (he_EH : e.onLine EH) (hh_EH : h.onLine EH)
    (heh : e ≠ h) (hbh : h ≠ b) (hhc : h ≠ c)
    (h_perp_ehb : ∠ e:h:b = ∟) :
    |(h─c)| * |(h─c)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)| := by
  -- ∠e:h:c = ∟: EH ⊥ BC at h, c another point on BC (h≠c); SMT uses perpendicular + collinearity
  have h_ehc : ∠ e:h:c = ∟ := by euclid_finish
  -- equal radii: |e─c| = |e─b|
  have h_rad : |(e─c)| = |(e─b)| := by euclid_finish
  have h_rad_sq : |(e─c)| * |(e─c)| = |(e─b)| * |(e─b)| := by rw [h_rad]
  -- Pythagorean in triangle ehc
  euclid_apply (line_from_points e h) as EHl
  euclid_apply (line_from_points e c) as EC
  have htri : formTriangle h e c EHl EC BC := by euclid_finish
  have hp := Elements.Book1.proposition_47 h e c EHl EC BC ⟨htri, h_ehc⟩
  -- hp : |(e─c)| * |(e─c)| = |(e─h)| * |(e─h)| + |(h─c)| * |(h─c)|
  linarith [hp, h_rad_sq]

end Elements.Book3
