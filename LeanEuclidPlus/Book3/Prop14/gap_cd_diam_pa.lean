import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagoras for the right triangle a-f-e (right angle at the foot f on AB).
-- Robust to the degenerate coincidences a = f and e = f.
theorem helper_3_14_gap_cd_diam_pa
    (a e f : Point) (ABDC : Circle) (AB : Line)
    (ha : a.onCircle ABDC)
    (hcen : e.isCentre ABDC)
    (haAB : a.onLine AB) (hfAB : f.onLine AB)
    (hfangle : ∠ a:f:e = ∟) :
    |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| = |(a─e)| * |(a─e)| := by
  by_cases haf : a = f
  · have h0 : |(a─f)| = 0 := zero_segment_onlyif a f haf
    have hr : |(f─e)| = |(a─e)| := by euclid_finish
    rw [h0, hr]; ring
  · by_cases hef : e = f
    · have h0 : |(f─e)| = 0 := zero_segment_onlyif f e hef.symm
      have hr : |(a─f)| = |(a─e)| := by euclid_finish
      rw [h0, hr]; ring
    · euclid_apply (line_from_points a e) as AE
      euclid_apply (line_from_points f e) as FE
      have h_e_off : ¬ e.onLine AB := by euclid_finish
      have htri : formTriangle f a e AB AE FE := by euclid_finish
      have hp : |(a─e)| * |(a─e)| = |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| := by
        euclid_apply (Elements.Book1.proposition_47 f a e AB AE FE)
        euclid_finish
      linarith [hp]

end Elements.Book3
