import SystemE
import Book1.Prop19.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_24_step10_nondeg
  (a b c d e f g g' g'' : Point) (AB BC AC DE EF DF DG EG FG : Line)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab_ne : a ≠ b)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
  (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
  (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_de_ne : d ≠ e)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
  (h_f_DF : f.onLine DF) (h_d_DF : d.onLine DF)
  (h_DE_ne_EF : DE ≠ EF) (h_EF_ne_DF : EF ≠ DF) (h_DF_ne_DE : DF ≠ DE)
  (h_d_DG : d.onLine DG) (h_g'_DG : g'.onLine DG) (h_between_g' : between d g' g'')
  (h_g'_sf_or_on : g'.onLine DE ∨ g'.sameSide f DE)
  (h_g'_angle : ∠ g':d:e = ∠ b:a:c)
  (h_g''_DG : g''.onLine DG) (h_between_g : between d g g'')
  (h_e_EG : e.onLine EG) (h_g_EG : g.onLine EG)
  (h_g_FG : g.onLine FG) (h_f_FG : f.onLine FG)
  (h_step3 : distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG)
  (h_step1 : ∠ e:d:g = ∠ b:a:c) (h_bac_gt : ∠ b:a:c > ∠ e:d:f)
  (hassump1 : ∠ e:f:g > ∠ e:g:f)
  (h_g_EF : ¬g.onLine EF)
  : |(e─g)| > |(e─f)| := by
  have h_ef_ne : e ≠ f := by euclid_finish
  have h_EF_ne_FG : EF ≠ FG := fun h => h_g_EF (h ▸ h_g_FG)
  have h_FG_ne_EG : FG ≠ EG := by euclid_finish
  have h_EG_ne_EF : EG ≠ EF := by euclid_finish
  have h_tri : formTriangle e f g EF FG EG :=
    ⟨⟨h_e_EF, h_f_EF, h_ef_ne⟩, h_f_FG, h_g_FG, h_g_EG, h_e_EG,
     h_EF_ne_FG, h_FG_ne_EG, h_EG_ne_EF⟩
  have h_ineq : ∠ e:f:g > ∠ f:g:e := by euclid_finish
  euclid_apply (proposition_19 e f g EF FG EG)
  euclid_finish

end Elements.Book1
