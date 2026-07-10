import SystemE
import Book1.Prop08.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

theorem helper_3_9_step5
    (ABC : Circle) (a b d e : Point) (AB GK : Line)
    (hd_inside : d.insideCircle ABC)
    (ha_ABC : a.onCircle ABC) (hb_ABC : b.onCircle ABC)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (he_GK : e.onLine GK) (hd_GK : d.onLine GK)
    (haeb : between a e b)
    (he_ne_d : e ≠ d)
    (hstep3 : |(a─e)| = |(b─e)| ∧ |(e─d)| = |(e─d)|)
    (hstep4 : |(d─a)| = |(d─b)|)
    : ∠ a:e:d = ∠ b:e:d := by
  have he_AB : e.onLine AB := between_same_line_in a e b AB ⟨haeb, ha_AB, hb_AB⟩
  have hda : d ≠ a := by euclid_finish
  have hdb : d ≠ b := by euclid_finish
  have hae : a ≠ e := by euclid_finish
  have hbe : b ≠ e := by euclid_finish
  obtain ⟨AD, ha_AD, hd_AD⟩ := line_from_points a d hda.symm
  obtain ⟨BD, hb_BD, hd_BD⟩ := line_from_points b d hdb.symm
  have hform_ead : formTriangle e a d AB AD GK := by euclid_finish
  have hform_ebd : formTriangle e b d AB BD GK := by euclid_finish
  have hea_eb : |(e─a)| = |(e─b)| := by
    linarith [segment_symmetric a e, segment_symmetric b e, hstep3.1]
  have had_bd : |(a─d)| = |(b─d)| := by
    linarith [segment_symmetric d a, segment_symmetric d b, hstep4]
  euclid_apply (proposition_8 e a d e b d AB AD GK AB BD GK ⟨hform_ead, hform_ebd, hea_eb, rfl, had_bd⟩)

end Elements.Book3
