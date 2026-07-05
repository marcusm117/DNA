import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step1 (b c e f g h : Point) (AH BG HG BE CH : Line)
  (h_b_BG : b.onLine BG) (h_c_BG : c.onLine BG)
  (h_e_AH : e.onLine AH) (h_h_AH : h.onLine AH)
  (h_f_BG : f.onLine BG) (h_g_BG : g.onLine BG)
  (h_h_HG : h.onLine HG) (h_g_HG : g.onLine HG) (h_h_ne_g : h ≠ g)
  (h_ss : e.sameSide f HG)
  (h_par : ¬AH.intersectsLine BG)
  (h_b_BE : b.onLine BE) (h_e_BE : e.onLine BE)
  (h_c_CH : c.onLine CH) (h_h_CH : h.onLine CH) :
  distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH := by
  have h_AH_ne_BG : AH ≠ BG := by
    intro h_AH_BG
    have h_g_AH : g.onLine AH := h_AH_BG.symm ▸ h_g_BG
    have h_dp_hg : distinctPointsOnLine h g HG := ⟨h_h_HG, h_g_HG, h_h_ne_g⟩
    have h_HG_AH : HG = AH := two_points_determine_line h g HG AH ⟨h_dp_hg, h_h_AH, h_g_AH⟩
    exact (same_side_not_on_line e f HG h_ss) (h_HG_AH.symm ▸ h_e_AH)
  refine ⟨⟨h_b_BE, h_e_BE, ?_⟩, ⟨h_c_CH, h_h_CH, ?_⟩⟩
  · intro h_eq; subst h_eq
    exact h_par (intersection_lines_common_point b AH BG ⟨h_e_AH, h_b_BG, h_AH_ne_BG⟩)
  · intro h_eq; subst h_eq
    exact h_par (intersection_lines_common_point c AH BG ⟨h_h_AH, h_c_BG, h_AH_ne_BG⟩)

end Elements.Book1
