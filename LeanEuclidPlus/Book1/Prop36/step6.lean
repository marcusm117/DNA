import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_36_step6 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
  (h_a_AH : a.onLine AH) (h_e_AH : e.onLine AH) (h_h_AH : h.onLine AH)
  (h_b_BG : b.onLine BG) (h_c_BG : c.onLine BG)
  (h_d_AH : d.onLine AH)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
  (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD) (h_d_ne_c : d ≠ c)
  (h_ss_ab_CD : a.sameSide b CD)
  (h_ab_ne_cd : ¬AB.intersectsLine CD)
  (h_b_BE : b.onLine BE) (h_e_BE : e.onLine BE)
  (h_c_CH : c.onLine CH) (h_h_CH : h.onLine CH)
  (h_par : ¬AH.intersectsLine BG)
  (h_step4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH)
  (h_step5 : |(e─b)| = |(h─c)| ∧ ¬BE.intersectsLine CH)
  (h_bet : between a e h)
  (h_bet_adh : between a d h) :
  formParallelogram e h b c AH BG BE CH := by
  have h_dp_HC : distinctPointsOnLine h c CH := h_step4.2
  have h_ne_be_ch : ¬BE.intersectsLine CH := h_step5.2
  have h_e_ne_h : e ≠ h := by
    have hbetrev := (between_symm a e h h_bet).1
    exact (between_symm h e a hbetrev).2.1.symm
  have h_dp_eh_AH : distinctPointsOnLine e h AH := ⟨h_e_AH, h_h_AH, h_e_ne_h⟩
  have h_ne_hc : h ≠ c := h_dp_HC.2.2
  have h_b_not_CD : ¬b.onLine CD := by
    apply same_side_not_on_line (a := b) (b := a)
    exact same_side_symm a b CD h_ss_ab_CD
  have h_b_ne_c : b ≠ c := fun h_eq => h_b_not_CD (h_eq ▸ h_c_CD)
  have h_dp_bc_BG : distinctPointsOnLine b c BG := ⟨h_b_BG, h_c_BG, h_b_ne_c⟩
  have step6_ss_ssa : e.sameSide a CH := by sorry
  have step6_ss_ssb : a.sameSide b CH := by sorry
  have step6_ss : e.sameSide b CH := by sorry
  euclid_apply (proposition_34' a d b c AH BG AB CD)
  exact ⟨h_e_AH, h_h_AH, h_b_BG, h_c_BG, h_e_BE, h_b_BE, ⟨h_h_CH, h_c_CH, h_ne_hc⟩, step6_ss, h_par, h_ne_be_ch⟩

end Elements.Book1
