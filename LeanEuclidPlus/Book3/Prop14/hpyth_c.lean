import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagoras for the right triangle c-g-e (right angle at the foot g).
-- Robust to the degenerate coincidences c = g and e = g (identity still holds).
theorem helper_3_14_hpyth_c
    (a c e g : Point) (ABDC : Circle) (CD : Line)
    (ha : a.onCircle ABDC) (hc : c.onCircle ABDC)
    (hcen : e.isCentre ABDC)
    (hcCD : c.onLine CD) (hgCD : g.onLine CD)
    (hgangle : ∠ c:g:e = ∟) :
    |(c─g)| * |(c─g)| + |(g─e)| * |(g─e)| = |(a─e)| * |(a─e)| := by
  by_cases hcg : c = g
  · -- c = g on the circle, |cg| = 0.
    have h0 : |(c─g)| = 0 := zero_segment_onlyif c g hcg
    have hr : |(g─e)| = |(a─e)| := by euclid_finish
    rw [h0, hr]; ring
  · by_cases heg : e = g
    · -- e = g, |ge| = 0.
      have h0 : |(g─e)| = 0 := zero_segment_onlyif g e heg.symm
      have hr : |(c─g)| = |(a─e)| := by euclid_finish
      rw [h0, hr]; ring
    · -- proper right triangle g-c-e.
      euclid_apply (line_from_points c e) as CE
      euclid_apply (line_from_points g e) as GE
      have hce_ne : c ≠ e := by euclid_finish
      have h_e_off : ¬ e.onLine CD := by euclid_finish
      have htri : formTriangle g c e CD CE GE := by euclid_finish
      have hp : |(c─e)| * |(c─e)| = |(c─g)| * |(c─g)| + |(g─e)| * |(g─e)| := by
        euclid_apply (Elements.Book1.proposition_47 g c e CD CE GE)
        euclid_finish
      have hce_ae : |(c─e)| = |(a─e)| := by euclid_finish
      have hsq : |(a─e)| * |(a─e)| = |(c─e)| * |(c─e)| := by rw [hce_ae]
      linarith [hp, hsq]

end Elements.Book3
