import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

theorem helper_3_9_hcentre_perp_d
    (a b d e : Point) (AB ED : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (he_AB : e.onLine AB)
    (he_ED : e.onLine ED) (hd_ED : d.onLine ED)
    (haeb : between a e b) (hae_eb : |(a─e)| = |(e─b)|)
    (h_da_db : |(d─a)| = |(d─b)|)
    (hdAB : ¬d.onLine AB)
    (hed : e ≠ d)
    (hda : d ≠ a)
    : ∠ a:e:d = ∟ := by
  have hdb : d ≠ b := by euclid_finish
  have hae : a ≠ e := by euclid_finish
  have hbe : b ≠ e := by euclid_finish
  obtain ⟨AD, ha_AD, hd_AD⟩ := line_from_points a d hda.symm
  obtain ⟨BD, hb_BD, hd_BD⟩ := line_from_points b d hdb.symm
  have hform_ead : formTriangle e a d AB AD ED := by euclid_finish
  have hform_ebd : formTriangle e b d AB BD ED := by euclid_finish
  have hea_eb : |(e─a)| = |(e─b)| := by linarith [segment_symmetric a e, hae_eb]
  have had_bd : |(a─d)| = |(b─d)| := by
    linarith [segment_symmetric d a, segment_symmetric d b, h_da_db]
  have h5 : ∠ a:e:d = ∠ b:e:d :=
    proposition_8 e a d e b d AB AD ED AB BD ED ⟨hform_ead, hform_ebd, hea_eb, rfl, had_bd⟩
  exact perpendicular_if a b e d AB
    ⟨ha_AB, hb_AB, haeb, hdAB, h5.trans (angle_symm b e d ⟨hbe, hed⟩)⟩

end Elements.Book3
