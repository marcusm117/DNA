import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_36_step5_ss_ssa (a b c d e h : Point) (AH BG AB CD CH : Line)
  (h_a_AH : a.onLine AH) (h_e_AH : e.onLine AH) (h_h_AH : h.onLine AH)
  (h_b_BG : b.onLine BG) (h_c_BG : c.onLine BG)
  (h_d_AH : d.onLine AH)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
  (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD) (h_d_ne_c : d ≠ c)
  (h_ss_ab_CD : a.sameSide b CD)
  (h_ab_ne_cd : ¬AB.intersectsLine CD)
  (h_c_CH : c.onLine CH) (h_h_CH : h.onLine CH)
  (h_par : ¬AH.intersectsLine BG)
  (h_dp_HC : distinctPointsOnLine h c CH)
  (h_dp_eh_AH : distinctPointsOnLine e h AH)
  (h_bet : between a e h) :
  e.sameSide a CH := by
  have h_dp_dc_CD : distinctPointsOnLine d c CD := ⟨h_d_CD, h_c_CD, h_d_ne_c⟩
  have h_pgram1 : formParallelogram a d b c AH BG AB CD :=
    ⟨h_a_AH, h_d_AH, h_b_BG, h_c_BG, h_a_AB, h_b_AB, h_dp_dc_CD, h_ss_ab_CD, h_par, h_ab_ne_cd⟩
  have h_pgram_ss := parallelogram_same_side a d b c AH BG AB CD h_pgram1
  have h_b_ss_c_AH : b.sameSide c AH := h_pgram_ss.2.1
  have h_b_not_AH : ¬b.onLine AH := same_side_not_on_line b c AH h_b_ss_c_AH
  have h_AH_ne_BG : AH ≠ BG := by
    intro h_eq; apply h_b_not_AH; rw [h_eq]; exact h_b_BG
  have h_AH_ne_CH : AH ≠ CH := fun h_eq =>
    h_par (intersection_lines_common_point c AH BG ⟨h_eq ▸ h_c_CH, h_c_BG, h_AH_ne_BG⟩)
  have h_ne_e_CH : ¬e.onLine CH := fun h_e_CH =>
    h_AH_ne_CH (two_points_determine_line e h AH CH ⟨h_dp_eh_AH, h_e_CH, h_h_CH⟩)
  have h_bet_hea : between h e a := (between_symm a e h h_bet).1
  euclid_apply (pasch_2 h e a CH)
  assumption

end Elements.Book1
