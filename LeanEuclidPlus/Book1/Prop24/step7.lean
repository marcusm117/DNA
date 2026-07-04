import SystemE
import Book.Prop05
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_24_step7
  (a b c d e g f g' g'' : Point) (AB BC AC DE EF DF DG EG FG : Line)
  -- formTriangle a b c atoms (for ruling out g'.onLine DE)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab_ne : a ≠ b)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
  (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
  -- Triangle DEF atoms
  (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_de_ne : d ≠ e)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
  (h_f_DF : f.onLine DF) (h_d_DF : d.onLine DF)
  (h_EF_ne_DF : EF ≠ DF) (h_DF_ne_DE : DF ≠ DE)
  -- DG line and construction points
  (h_d_DG : d.onLine DG)
  (h_g'_DG : g'.onLine DG) (h_between_g' : between d g' g'')
  (h_g'_sf_or_on : g'.onLine DE ∨ g'.sameSide f DE)
  (h_g'_angle : ∠ g':d:e = ∠ b:a:c)
  (h_g''_DG : g''.onLine DG) (h_between_g : between d g g'')
  -- EG and FG lines
  (h_e_EG : e.onLine EG) (h_g_EG : g.onLine EG)
  (h_g_FG : g.onLine FG) (h_f_FG : f.onLine FG)
  -- From previous steps
  (h_step3 : distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG)
  (h_step4 : |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)|)
  (h_step1 : ∠ e:d:g = ∠ b:a:c) (h_bac_gt : ∠ b:a:c > ∠ e:d:f)
  (hassump1 : |(d─f)| = |(d─g)|)
  : ∠ d:g:f = ∠ d:f:g := by
  have h_g_DG : g.onLine DG := by euclid_finish
  have h_g_ne_d : g ≠ d := by euclid_finish
  have h_f_ne_g : f ≠ g := h_step3.2.2.2
  have h_f_ne_d : f ≠ d := by euclid_finish
  have h_edg_gt : ∠ e:d:g > ∠ e:d:f := by rw [h_step1]; exact h_bac_gt
  -- g' is on f's side of DE: rule out g'.onLine DE using formTriangle abc
  -- (if g' on DE: ∠g':d:e = 0 or 2π, but ∠g':d:e = ∠b:a:c, a triangle angle > 0)
  have h_g'_sf_f : g'.sameSide f DE := by
    rcases h_g'_sf_or_on with h | h
    · exact absurd h_g'_angle (by euclid_finish)
    · exact h
  -- g is between d and g'' just like g', so g is also on f's side of DE
  have h_g_sf_f : g.sameSide f DE := by euclid_finish
  -- DG ≠ DF: if DG = DF, then g on DF at |dg|=|df| from d, on f's side of DE → g = f. Contradicts f≠g.
  have h_DG_ne_DF : DG ≠ DF := by
    intro h_eq
    have h_g_DF : g.onLine DF := h_eq ▸ h_g_DG
    have h_g_eq_f : g = f := by euclid_finish
    exact absurd h_g_eq_f h_f_ne_g.symm
  -- DG ≠ FG: if DG = FG then d on FG; with d,f on DG=FG and f≠d → DF = DG. Contradicts h_DG_ne_DF.
  have h_DG_ne_FG : DG ≠ FG := by
    intro h_eq
    have h_d_FG : d.onLine FG := h_eq ▸ h_d_DG
    have h_f_DG : f.onLine DG := h_eq.symm ▸ h_f_FG
    exact absurd (show DF = DG from by euclid_finish) h_DG_ne_DF.symm
  -- FG ≠ DF: if FG = DF then g on DF; with d,g on DG and DF and g≠d → DG = DF. Contradicts h_DG_ne_DF.
  have h_FG_ne_DF : FG ≠ DF := by
    intro h_eq
    have h_g_DF : g.onLine DF := h_eq ▸ h_g_FG
    exact absurd (show DG = DF from by euclid_finish) h_DG_ne_DF
  -- Assemble formTriangle d g f DG FG DF from atoms
  have h_tri_dgf : formTriangle d g f DG FG DF :=
    ⟨⟨h_d_DG, h_g_DG, h_g_ne_d.symm⟩, h_g_FG, h_f_FG, h_f_DF, h_d_DF,
     h_DG_ne_FG, h_FG_ne_DF, h_DG_ne_DF.symm⟩
  -- Apply proposition_5': isosceles base angles equal (|dg| = |df|, so ∠dgf = ∠dfg)
  exact proposition_5' d g f DG FG DF ⟨h_tri_dgf, hassump1.symm⟩

end Elements.Book1
