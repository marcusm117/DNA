import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_24_step8_same
  (a b c d e f g g' g'' : Point) (AB BC AC DE EF DF DG EG FG : Line)
  -- formTriangle abc atoms (to rule out g'.onLine DE)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab_ne : a ≠ b)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
  (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
  -- formTriangle def atoms
  (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_de_ne : d ≠ e)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
  (h_f_DF : f.onLine DF) (h_d_DF : d.onLine DF)
  (h_DE_ne_EF : DE ≠ EF) (h_EF_ne_DF : EF ≠ DF) (h_DF_ne_DE : DF ≠ DE)
  -- DG line and construction points
  (h_d_DG : d.onLine DG) (h_g'_DG : g'.onLine DG) (h_between_g' : between d g' g'')
  (h_g'_sf_or_on : g'.onLine DE ∨ g'.sameSide f DE)
  (h_g'_angle : ∠ g':d:e = ∠ b:a:c)
  (h_g''_DG : g''.onLine DG) (h_between_g : between d g g'')
  -- EG and FG lines
  (h_e_EG : e.onLine EG) (h_g_EG : g.onLine EG)
  (h_g_FG : g.onLine FG) (h_f_FG : f.onLine FG)
  -- Previous steps and case hypothesis
  (h_step3 : distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG)
  (h_step1 : ∠ e:d:g = ∠ b:a:c) (h_bac_gt : ∠ b:a:c > ∠ e:d:f)
  (hassump1 : |(d─f)| = |(d─g)|)
  (h_step7 : ∠ d:g:f = ∠ d:f:g)
  (h_same : d.sameSide g EF)
  : ∠ d:f:g > ∠ e:g:f := by
  have h_g_DG : g.onLine DG := by euclid_finish
  have h_g_ne_d : g ≠ d := by euclid_finish
  have h_f_ne_g : f ≠ g := h_step3.2.2.2
  have h_f_ne_d : f ≠ d := by euclid_finish
  have h_edg_gt : ∠ e:d:g > ∠ e:d:f := by rw [h_step1]; exact h_bac_gt
  -- g is on f's side of DE (from g' construction)
  have h_g'_sf_f : g'.sameSide f DE := by
    rcases h_g'_sf_or_on with h | h
    · exact absurd h_g'_angle (by euclid_finish)
    · exact h
  have h_g_sf_f : g.sameSide f DE := by euclid_finish
  -- DG ≠ DF (needed for triple_incidence_2 distinctness)
  have h_DG_ne_DF : DG ≠ DF := by
    intro h_eq
    have h_g_DF : g.onLine DF := h_eq ▸ h_g_DG
    exact absurd (show g = f from by euclid_finish) h_f_ne_g.symm
  -- g is not on DF (if it were, |dg|=|df| and g on f's side of DE → g=f)
  have h_g_off_DF : ¬(g.onLine DF) := by euclid_finish
  -- e and g are on opposite sides of DF (g inside angle, e on one ray)
  have h_e_opp_g_DF : ¬(e.sameSide g DF) := by euclid_finish
  -- triple_incidence_2 at d (on DE, DF, DG): e.sameSide f DG
  euclid_apply (triple_incidence_2 DE DF DG d e f g)
  -- d and e are on the same side of FG
  have h_d_sf_e_FG : d.sameSide e FG := by euclid_finish
  -- sum_angles_onlyif at g: ∠d:g:f = ∠d:g:e + ∠e:g:f
  euclid_apply (sum_angles_onlyif g d f e DG FG)
  -- ∠d:g:e > 0 since d, g, e are non-collinear
  have h_dge_pos : ∠ d:g:e > 0 := by euclid_finish
  -- From step7: ∠d:g:f = ∠d:f:g; from sum_angles: ∠d:g:f = ∠d:g:e + ∠e:g:f
  -- Therefore ∠d:f:g = ∠d:g:e + ∠e:g:f > ∠e:g:f
  linarith

end Elements.Book1
