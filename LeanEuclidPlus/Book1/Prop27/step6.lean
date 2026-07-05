import SystemE
import Book.Prop16
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step6
  (a d e f b g : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (h_ae : a ≠ e)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD) (_ : f ≠ d)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_angle : ∠ a:e:f = ∠ e:f:d)
  (h_a_off_EF : ¬a.onLine EF) (h_d_off_EF : ¬d.onLine EF) (_ : ¬a.sameSide d EF)
  (_ : AE.intersectsLine FD)
  (h_b_AE : b.onLine AE) (h_bae : between a e b)
  (h_g_AE : g.onLine AE) (h_g_FD : g.onLine FD)
  : ¬(g.opposingSides b EF) := by
  intro h_opp
  have h_g_off : ¬g.onLine EF := h_opp.1
  have h_b_off : ¬b.onLine EF := h_opp.2.1
  have h_gb_opp : ¬g.sameSide b EF := h_opp.2.2
  have h_ab_opp : ¬a.sameSide b EF := pasch_3 a e b EF ⟨h_bae, h_e_EF⟩
  -- g and b opposite sides, a and b opposite sides → g and a same side
  have h_bg_opp : ¬b.sameSide g EF := fun h => h_gb_opp (same_side_symm b g EF h)
  have h_ba_opp : ¬b.sameSide a EF := fun h => h_ab_opp (same_side_symm b a EF h)
  have h_pigeon := same_side_pigeon_hole b g a EF ⟨h_b_off, h_g_off, h_a_off_EF⟩
  have h_ga_same : g.sameSide a EF := by tauto
  have h_not_btwn_aeg : ¬between a e g := fun h =>
    absurd (same_side_symm g a EF h_ga_same) (pasch_3 a e g EF ⟨h, h_e_EF⟩)
  have h_not_btwn_fef : ¬between f e f := fun h =>
    absurd rfl ((between_symm f e f h).2.2.1)
  have h_ge : g ≠ e := fun h => h_g_off (h ▸ h_e_EF)
  have h_fe : f ≠ e := Ne.symm h_ef
  have h_eq : ∠ a:e:f = ∠ g:e:f :=
    equal_angles e a g f f AE EF
      ⟨h_e_AE, h_a_AE, h_g_AE, h_e_EF, h_f_EF, h_f_EF,
       h_ae, h_ge, h_fe, h_fe, h_not_btwn_aeg, h_not_btwn_fef⟩
  have h_tri : formTriangle e g f AE FD EF := by euclid_finish
  have h_gfd : between g f d := by euclid_finish
  have h16 := proposition_16 e g f d AE FD EF ⟨h_tri, h_gfd⟩
  linarith [h16.2, h_eq, h_angle]

end Elements.Book1
