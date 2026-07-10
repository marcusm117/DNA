import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

theorem helper_3_9_hcentre_perp_o
    (ABC : Circle) (a b e o : Point) (AB : Line)
    (ha : a.onCircle ABC) (hb : b.onCircle ABC)
    (ho : o.isCentre ABC)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (he_AB : e.onLine AB)
    (haeb : between a e b) (hae_eb : |(a─e)| = |(e─b)|)
    (hoAB : ¬o.onLine AB)
    : ∠ a:e:o = ∟ := by
  have hoa : a ≠ o := by euclid_finish
  have hob : b ≠ o := by euclid_finish
  have hoe : o ≠ e := by euclid_finish
  have hae : a ≠ e := by euclid_finish
  have hbe : b ≠ e := by euclid_finish
  have hoa_ob : |(o─a)| = |(o─b)| := by
    linarith [point_on_circle_onlyif o a b ABC ⟨ho, ha, hb⟩]
  obtain ⟨OE, ho_OE, he_OE⟩ := line_from_points o e hoe
  obtain ⟨OA, ho_OA, ha_OA⟩ := line_from_points o a hoa.symm
  obtain ⟨OB, ho_OB, hb_OB⟩ := line_from_points o b hob.symm
  have hform_eao : formTriangle e a o AB OA OE := by euclid_finish
  have hform_ebo : formTriangle e b o AB OB OE := by euclid_finish
  have hea_eb : |(e─a)| = |(e─b)| := by linarith [segment_symmetric a e, hae_eb]
  have hao_bo : |(a─o)| = |(b─o)| := by
    linarith [segment_symmetric o a, segment_symmetric o b, hoa_ob]
  have h6 : ∠ a:e:o = ∠ b:e:o :=
    proposition_8 e a o e b o AB OA OE AB OB OE ⟨hform_eao, hform_ebo, hea_eb, rfl, hao_bo⟩
  exact perpendicular_if a b e o AB
    ⟨ha_AB, hb_AB, haeb, hoAB, h6.trans (angle_symm b e o ⟨hbe, hoe.symm⟩)⟩

end Elements.Book3
