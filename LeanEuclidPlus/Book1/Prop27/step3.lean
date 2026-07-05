import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step3
  (a d e f g b : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (_ : a ≠ e)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD) (h_fd : f ≠ d)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_a_off_EF : ¬a.onLine EF) (h_d_off_EF : ¬d.onLine EF) (_ : ¬a.sameSide d EF)
  (h_angle : ∠ a:e:f = ∠ e:f:d)
  (h_b_AE : b.onLine AE) (h_bae : between a e b)
  (h_g_AE : g.onLine AE) (h_g_FD : g.onLine FD)
  (hbd : g.sameSide b EF)
  : ∠ a:e:f = ∠ e:f:g := by
  have h_b_off_EF : ¬b.onLine EF := by euclid_finish
  have h_gf : g ≠ f := by euclid_finish
  have h_ab_off : ¬a.sameSide b EF :=
    pasch_3 a e b EF ⟨h_bae, h_e_EF⟩
  have h_db_same : d.sameSide b EF := by
    have := same_side_pigeon_hole a d b EF ⟨h_a_off_EF, h_d_off_EF, h_b_off_EF⟩
    tauto
  have h_gd_same : g.sameSide d EF :=
    same_side_symm d g EF
      (same_side_trans b d g EF
        ⟨same_side_symm d b EF h_db_same, same_side_symm g b EF hbd⟩)
  have h_not_between : ¬between g f d := fun h =>
    absurd h_gd_same (pasch_3 g f d EF ⟨h, h_f_EF⟩)
  have h_not_between_ee : ¬between e f e := fun h =>
    absurd rfl ((between_symm e f e h).2.2.1)
  have h_fe : f ≠ e := Ne.symm h_ef
  have h_df : d ≠ f := Ne.symm h_fd
  have h_symm1 : ∠ g:f:e = ∠ e:f:g := angle_symm g f e ⟨h_gf, h_fe⟩
  have h_symm2 : ∠ d:f:e = ∠ e:f:d := angle_symm d f e ⟨h_df, h_fe⟩
  have h_eq_mid : ∠ g:f:e = ∠ d:f:e :=
    equal_angles f g d e e FD EF
      ⟨h_f_FD, h_g_FD, h_d_FD, h_f_EF, h_e_EF, h_e_EF,
       h_gf, h_df, h_ef, h_ef, h_not_between, h_not_between_ee⟩
  linarith

end Elements.Book1
