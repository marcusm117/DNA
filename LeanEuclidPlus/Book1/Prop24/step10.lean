import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop24.step10_deg
import Book1.Prop24.step10_nondeg
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_24_step10
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
  : |(e─g)| > |(e─f)| := by
  by_cases h_g_EF : g.onLine EF
  · -- Degenerate: g, e, f collinear on EF → between e f g → |eg| > |ef|
    have step10_deg : |(e─g)| > |(e─f)| := by euclid_apply (helper_1_24_step10_deg a b c d e f g g' g'' AB BC AC DE EF DF DG EG FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show DE ≠ EF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g'.onLine DG; assumption)) (by euclid_assumption "" (show between d g' g''; assumption)) (by euclid_assumption "" (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by euclid_assumption "" (show ∠ g':d:e = ∠ b:a:c; assumption)) (by euclid_assumption "" (show g''.onLine DG; assumption)) (by euclid_assumption "" (show between d g g''; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by euclid_assumption "" (show ∠ e:d:g = ∠ b:a:c; assumption)) (by euclid_assumption "" (show ∠ b:a:c > ∠ e:d:f; assumption)) (by euclid_assumption "" (show ∠ e:f:g > ∠ e:g:f; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)))
    exact step10_deg
  · -- Non-degenerate: formTriangle e f g EF FG EG → proposition_19
    have step10_nondeg : |(e─g)| > |(e─f)| := by euclid_apply (helper_1_24_step10_nondeg a b c d e f g g' g'' AB BC AC DE EF DF DG EG FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show DE ≠ EF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g'.onLine DG; assumption)) (by euclid_assumption "" (show between d g' g''; assumption)) (by euclid_assumption "" (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by euclid_assumption "" (show ∠ g':d:e = ∠ b:a:c; assumption)) (by euclid_assumption "" (show g''.onLine DG; assumption)) (by euclid_assumption "" (show between d g g''; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by euclid_assumption "" (show ∠ e:d:g = ∠ b:a:c; assumption)) (by euclid_assumption "" (show ∠ b:a:c > ∠ e:d:f; assumption)) (by euclid_assumption "" (show ∠ e:f:g > ∠ e:g:f; assumption)) (by euclid_assumption "" (show ¬g.onLine EF; assumption)))
    exact step10_nondeg

end Elements.Book1
