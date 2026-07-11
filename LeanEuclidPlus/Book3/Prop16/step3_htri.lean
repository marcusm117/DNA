import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_16_step3_htri
    (d a c e b : Point) (DA AE DC : Line)
    (left_3 : between a d b)
    (right_4 : ∠ e:a:b = ∟)
    (left_5 : a.onLine AE)
    (left_6 : e.onLine AE)
    (hcAE : c.onLine AE)
    (hDCd : d.onLine DC)
    (hDCc : c.onLine DC)
    (hDAd : d.onLine DA)
    (hDAa : a.onLine DA)
    (hda : d ≠ a)
    (hcne : c ≠ a)
    (hae : a ≠ e)
    : formTriangle d a c DA AE DC := by
  have hb_DA : b.onLine DA := between_same_line_out a d b DA ⟨left_3, hDAa, hDAd⟩
  have hab : a ≠ b := (between_symm a d b left_3).2.2.1
  have hDA_ne_AE : DA ≠ AE := by
    intro heq
    have hb_AE : b.onLine AE := heq ▸ hb_DA
    by_cases hbet : between e a b
    · have h_flat := flat_angle_onlyif e a b hbet
      linarith [right_angle_pos, right_4.symm.trans h_flat]
    · have h_zero := degenerated_angle_if a e b AE ⟨hae, hab, left_5, left_6, hb_AE, hbet⟩
      linarith [right_angle_pos, right_4.symm.trans h_zero]
  have hd_off_AE : ¬d.onLine AE := by
    intro hd_on
    exact hDA_ne_AE (two_points_determine_line a d AE DA
      ⟨⟨left_5, hd_on, hda.symm⟩, hDAa, hDAd⟩).symm
  have hAE_ne_DC : AE ≠ DC := fun heq => hd_off_AE (heq ▸ hDCd)
  have hDC_ne_DA : DC ≠ DA := by
    intro heq
    have hc_DA : c.onLine DA := heq ▸ hDCc
    exact hDA_ne_AE (two_points_determine_line a c DA AE
      ⟨⟨hDAa, hc_DA, hcne.symm⟩, left_5, hcAE⟩)
  exact ⟨⟨hDAd, hDAa, hda⟩, left_5, hcAE, hDCc, hDCd, hDA_ne_AE, hAE_ne_DC, hDC_ne_DA⟩

end Elements.Book3
