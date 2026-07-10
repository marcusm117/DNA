import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_9_step6
    (ABC : Circle) (a b d e g : Point) (AB GK : Line)
    (hd_inside : d.insideCircle ABC) (ha_ABC : a.onCircle ABC) (hb_ABC : b.onCircle ABC)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (he_GK : e.onLine GK) (hd_GK : d.onLine GK)
    (haeb : between a e b) (he_ne_d : e ≠ d) (ha_ne_b : a ≠ b)
    (hstep3 : |(a─e)| = |(b─e)| ∧ |(e─d)| = |(e─d)|)
    (hstep4 : |(d─a)| = |(d─b)|)
    (hstep5 : ∠ a:e:d = ∠ b:e:d)
    (hbetween_gde : between g d e)
    : ∠ a:e:d = ∟ ∧ ∠ b:e:d = ∟ := by
  have he_AB : e.onLine AB := between_same_line_in a e b AB ⟨haeb, ha_AB, hb_AB⟩
  have hbe : b ≠ e := by euclid_finish
  have hed : e ≠ d := he_ne_d
  have hd_off_AB : ¬d.onLine AB := by
    intro hdAB
    have hGK_AB : GK = AB :=
      two_points_determine_line e d GK AB ⟨⟨he_GK, hd_GK, he_ne_d⟩, he_AB, hdAB⟩
    have hbet_adb : between a d b :=
      circle_line_intersections d a b AB ABC ⟨hdAB, ha_AB, hb_AB, hd_inside, ha_ABC, hb_ABC, ha_ne_b⟩
    have h1 := between_if a d b hbet_adb
    have h2 := between_if a e b haeb
    have hae := hstep3.1
    have hde := hstep4
    have h3 := segment_symmetric a e
    have h4 := segment_symmetric b e
    have h5 := segment_symmetric d a
    have h6 := segment_symmetric d b
    have heqd : d = e := by euclid_finish
    exact he_ne_d heqd.symm
  have hstep5' : ∠ a:e:d = ∠ d:e:b := hstep5.trans (angle_symm b e d ⟨hbe, hed⟩)
  have hperp : ∠ a:e:d = ∟ :=
    perpendicular_if a b e d AB ⟨ha_AB, hb_AB, haeb, hd_off_AB, hstep5'⟩
  exact ⟨hperp, hstep5.symm.trans hperp⟩

end Elements.Book3
