import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagoras for the right triangle b-f-e.  ∠b:f:e = ∟ from ∠a:f:e = ∟ and between a f b.
-- Robust to the degenerate coincidences b = f and e = f.
theorem helper_3_14_gap_cd_diam_pb
    (a b e f : Point) (ABDC : Circle) (AB : Line)
    (ha : a.onCircle ABDC) (hb : b.onCircle ABDC)
    (hcen : e.isCentre ABDC)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (hfangle : ∠ a:f:e = ∟) (hafb : between a f b) :
    |(b─f)| * |(b─f)| + |(f─e)| * |(f─e)| = |(a─e)| * |(a─e)| := by
  by_cases hbf : b = f
  · have h0 : |(b─f)| = 0 := zero_segment_onlyif b f hbf
    have hr : |(f─e)| = |(a─e)| := by euclid_finish
    rw [h0, hr]; ring
  · by_cases hef : e = f
    · have h0 : |(f─e)| = 0 := zero_segment_onlyif f e hef.symm
      have hr : |(b─f)| = |(a─e)| := by euclid_finish
      rw [h0, hr]; ring
    · have hbangle : ∠ b:f:e = ∟ := by euclid_finish
      euclid_apply (line_from_points b e) as BE
      euclid_apply (line_from_points f e) as FE
      have h_e_off : ¬ e.onLine AB := by euclid_finish
      have htri : formTriangle f b e AB BE FE := by euclid_finish
      have hp : |(b─e)| * |(b─e)| = |(b─f)| * |(b─f)| + |(f─e)| * |(f─e)| := by
        euclid_apply (Elements.Book1.proposition_47 f b e AB BE FE)
        euclid_finish
      have hbe_ae : |(b─e)| = |(a─e)| := by euclid_finish
      have hsq : |(a─e)| * |(a─e)| = |(b─e)| * |(b─e)| := by rw [hbe_ae]
      linarith [hp, hsq]

end Elements.Book3
