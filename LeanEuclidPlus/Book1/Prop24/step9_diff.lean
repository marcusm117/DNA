import SystemE
import Book.Prop13
import Book.Prop17
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_24_step9_diff
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
  (hassump1 : |(d─f)| = |(d─g)|)
  (h_step7 : ∠ d:g:f = ∠ d:f:g)
  (h_step8 : ∠ d:f:g > ∠ e:g:f)
  (h_same : ¬d.sameSide g EF)
  : ∠ e:f:g > ∠ e:g:f := by
  have h_g_DG : g.onLine DG := by euclid_finish
  have h_f_ne_g : f ≠ g := h_step3.2.2.2
  have h_e_ne_g : e ≠ g := h_step3.1.2.2
  have h_f_ne_d : f ≠ d := by euclid_finish
  have h_edg_gt : ∠ e:d:g > ∠ e:d:f := by rw [h_step1]; exact h_bac_gt
  have h_g'_sf_f : g'.sameSide f DE := by
    rcases h_g'_sf_or_on with h | h
    · exact absurd h_g'_angle (by euclid_finish)
    · exact h
  have h_g_sf_f : g.sameSide f DE := by euclid_finish
  have h_DG_ne_DF : DG ≠ DF := by
    intro h_eq; have h_g_DF := h_eq ▸ h_g_DG
    exact absurd (show g = f from by euclid_finish) h_f_ne_g.symm
  have h_g_off_DF : ¬(g.onLine DF) := by euclid_finish
  have h_e_opp_g_DF : ¬(e.sameSide g DF) := by euclid_finish
  have h_d_off_EF : ¬(d.onLine EF) := by euclid_finish
  -- Degenerate sub-case: g on EF → e, f, g collinear, ∠e:f:g = 2∟, ∠e:g:f = 0
  by_cases h_g_EF : g.onLine EF
  · have h_e_off_DF : ¬(e.onLine DF) := by euclid_finish
    have h_f_sf_e_DG : f.sameSide e DG := by euclid_finish
    euclid_apply (pasch_4 e f g DF EF)
    euclid_finish
  · -- Non-degenerate: extend FG beyond f
    have h_e_off_DF : ¬(e.onLine DF) := by euclid_finish
    euclid_apply (extend_point FG g f) as h
    euclid_apply (pasch_3 g f h EF)
    euclid_apply (pasch_3 g f h DF)
    euclid_apply (same_side_pigeon_hole d g h EF)
    euclid_apply (same_side_pigeon_hole e g h DF)
    euclid_apply (proposition_13 d f g h DF FG)
    euclid_apply (proposition_13 e f g h EF FG)
    euclid_apply (sum_angles_onlyif f d e h DF EF)
    euclid_apply (proposition_17 d g e DG EG DE)
    euclid_apply (proposition_17 d f e DF EF DE)
    have h_sum4 : ∠ e:f:g + ∠ g:f:d + ∠ d:f:e = ∟ + ∟ + ∟ + ∟ := by euclid_finish
    euclid_finish

end Elements.Book1
