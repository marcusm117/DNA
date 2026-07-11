import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagoras for the right triangle d-g-e.  The right angle ∠d:g:e = ∟ comes from
-- ∠c:g:e = ∟ together with `between c g d` (eg ⊥ the whole line CD).
-- Robust to the degenerate coincidences d = g and e = g.
theorem helper_3_14_hpyth_d
    (a c d e g : Point) (ABDC : Circle) (CD : Line)
    (ha : a.onCircle ABDC) (hc : c.onCircle ABDC) (hd : d.onCircle ABDC)
    (hcen : e.isCentre ABDC)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hgCD : g.onLine CD)
    (hgangle : ∠ c:g:e = ∟) (hcgd : between c g d) :
    |(d─g)| * |(d─g)| + |(g─e)| * |(g─e)| = |(a─e)| * |(a─e)| := by
  by_cases hdg : d = g
  · have h0 : |(d─g)| = 0 := zero_segment_onlyif d g hdg
    have hr : |(g─e)| = |(a─e)| := by euclid_finish
    rw [h0, hr]; ring
  · by_cases heg : e = g
    · have h0 : |(g─e)| = 0 := zero_segment_onlyif g e heg.symm
      have hr : |(d─g)| = |(a─e)| := by euclid_finish
      rw [h0, hr]; ring
    · have hdangle : ∠ d:g:e = ∟ := by euclid_finish
      euclid_apply (line_from_points d e) as DE
      euclid_apply (line_from_points g e) as GE
      have hde_ne : d ≠ e := by euclid_finish
      have h_e_off : ¬ e.onLine CD := by euclid_finish
      have htri : formTriangle g d e CD DE GE := by euclid_finish
      have hp : |(d─e)| * |(d─e)| = |(d─g)| * |(d─g)| + |(g─e)| * |(g─e)| := by
        euclid_apply (Elements.Book1.proposition_47 g d e CD DE GE)
        euclid_finish
      have hde_ae : |(d─e)| = |(a─e)| := by euclid_finish
      have hsq : |(a─e)| * |(a─e)| = |(d─e)| * |(d─e)| := by rw [hde_ae]
      linarith [hp, hsq]

end Elements.Book3
