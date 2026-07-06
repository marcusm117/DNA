import SystemE
import Helpers.OffLine
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step6_same (a b e f g c : Point) (AB BC AG EF CG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b) (h_AB_ne_BC : AB ≠ BC)
    (h_a_AG : a.onLine AG)
    (h_f_EF : f.onLine EF) (h_f_AG : f.onLine AG)
    (h_e_EF : e.onLine EF) (h_e_BC : e.onLine BC)
    (h_g_CG : g.onLine CG)
    (h_c_CG : c.onLine CG) (h_c_BC : c.onLine BC)
    (h_bet : between b e c)
    (h_par_AG_BC : ¬AG.intersectsLine BC)
    (h_par_CG_EF : ¬CG.intersectsLine EF) :
    f.sameSide e CG := by
  -- AG ≠ BC: a is on AG but off BC (from AB ≠ BC + two_points_determine_line)
  have h_a_not_BC : ¬a.onLine BC := by
    intro h_a_BC
    have h_AB_BC : AB = BC := by
      euclid_apply (two_points_determine_line a b AB BC)
      euclid_finish
    exact h_AB_ne_BC h_AB_BC
  have h_AG_ne_BC : AG ≠ BC := fun h => h_a_not_BC (h ▸ h_a_AG)
  -- f off BC (f on AG ∥ BC, AG ≠ BC)
  have h_f_not_BC : ¬f.onLine BC := fun h_f_BC =>
    h_par_AG_BC (by
      apply intersection_lines_common_point f AG BC
      exact ⟨h_f_AG, h_f_BC, h_AG_ne_BC⟩)
  -- EF ≠ BC (f on EF but off BC)
  have h_EF_ne_BC : EF ≠ BC := Elements.line_ne_of_offLine f EF BC h_f_EF h_f_not_BC
  -- CG ≠ EF: if CG = EF, then e.onLine CG, so CG = BC (e and c both on CG and BC, e ≠ c),
  --          giving ¬BC.intersectsLine EF, but e is on both → contradiction
  have h_CG_ne_EF : CG ≠ EF := by
    intro h_CG_EF
    have h_e_CG : e.onLine CG := h_CG_EF ▸ h_e_EF
    have h_CG_BC : CG = BC := by
      euclid_apply (two_points_determine_line e c CG BC)
      euclid_finish
    have h_BC_EF : BC.intersectsLine EF := by
      apply intersection_lines_common_point e BC EF
      exact ⟨h_e_BC, h_e_EF, h_EF_ne_BC.symm⟩
    exact (h_CG_BC ▸ h_par_CG_EF) h_BC_EF
  -- g off EF (g on CG, CG ≠ EF, CG ∥ EF)
  have h_g_not_EF : ¬g.onLine EF :=
    Elements.offLine_of_parallel_simple g CG EF h_g_CG h_CG_ne_EF h_par_CG_EF
  exact Elements.sameSide_of_parallel f e g EF CG h_f_EF h_e_EF h_g_CG h_g_not_EF h_par_CG_EF

end Elements.Book1
