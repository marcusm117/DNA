import SystemE
import Book.Prop33
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_36_step5 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
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
  (h_eq : |(b─c)| = |(e─h)|)
  (h_step4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH)
  (h_bet : between a e h)
  (h_bet_adh : between a d h) :
  |(e─b)| = |(h─c)| ∧ ¬BE.intersectsLine CH := by
  have h_dp_EB := h_step4.1
  have h_dp_HC := h_step4.2
  have h_bet_hea : between h e a := (between_symm a e h h_bet).1
  have h_e_ne_h : e ≠ h := (between_symm h e a h_bet_hea).2.1.symm
  have h_dp_eh_AH : distinctPointsOnLine e h AH := ⟨h_e_AH, h_h_AH, h_e_ne_h⟩
  have h_b_ne_c : b ≠ c := fun heq => by
    have hbc : |(b─c)| = 0 := by rw [heq]; exact zero_segment_onlyif c c rfl
    exact h_e_ne_h (zero_segment_if e h (h_eq.symm.trans hbc))
  have h_dp_bc_BG : distinctPointsOnLine b c BG := ⟨h_b_BG, h_c_BG, h_b_ne_c⟩
  have step5_ss_ssa : e.sameSide a CH := by sorry
  have step5_ss_ssb : a.sameSide b CH := by sorry
  have step5_ss : e.sameSide b CH := by sorry
  euclid_apply (proposition_33 e h b c AH BG BE CH)
  exact ⟨by assumption, by assumption⟩

end Elements.Book1
