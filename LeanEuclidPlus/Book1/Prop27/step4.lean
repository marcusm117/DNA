import SystemE
import Book.Prop16
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step4
  (a d e f b g : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (h_ae : a ≠ e)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD) (_ : f ≠ d)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (_ : ∠ a:e:f = ∠ e:f:d)
  (h_a_off_EF : ¬a.onLine EF) (_ : ¬d.onLine EF) (_ : ¬a.sameSide d EF)
  (_ : AE.intersectsLine FD)
  (h_b_AE : b.onLine AE) (h_bae : between a e b)
  (h_g_AE : g.onLine AE) (h_g_FD : g.onLine FD)
  (hbd : g.sameSide b EF)
  (h_step3 : ∠ a:e:f = ∠ e:f:g)
  : False := by
  have h_ab_opp : ¬a.sameSide b EF := pasch_3 a e b EF ⟨h_bae, h_e_EF⟩
  have h_b_off_EF : ¬b.onLine EF := by euclid_finish
  have h_g_off_EF : ¬g.onLine EF := by euclid_finish
  have h_ga_opp : ¬g.sameSide a EF := fun hga =>
    h_ab_opp (same_side_trans g a b EF ⟨hga, hbd⟩)
  have h_gea : between g e a := by euclid_finish
  have h_tri : formTriangle f g e FD AE EF := by euclid_finish
  have h_fe : f ≠ e := Ne.symm h_ef
  have h_ea : e ≠ a := Ne.symm h_ae
  have h_gf : g ≠ f := by euclid_finish
  have h_fea_eq : ∠ f:e:a = ∠ a:e:f := angle_symm f e a ⟨h_fe, h_ea⟩
  have h_gfe_eq : ∠ g:f:e = ∠ e:f:g := angle_symm g f e ⟨h_gf, h_fe⟩
  euclid_apply (proposition_16 f g e a FD AE EF)
  linarith

end Elements.Book1
