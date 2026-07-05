import SystemE
import Book.Prop04
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_24_step6
  (a b c d e g g'' : Point) (AB BC AC DE EG DG : Line)
  -- formTriangle ABC atoms
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab_ne : a ≠ b)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
  (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
  -- formTriangle DEG atoms from construction
  (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_de_ne : d ≠ e)
  (h_e_EG : e.onLine EG) (h_g_EG : g.onLine EG)
  (h_d_DG : d.onLine DG) (h_g''_DG : g''.onLine DG) (h_between_g : between d g g'')
  -- distinctness from step3
  (h_step3 : distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG)
  -- SAS conditions from steps 4 and 5
  (h_step4 : |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)|)
  (h_step5 : ∠ b:a:c = ∠ e:d:g)
  : |(b─c)| = |(e─g)| := by
  have h_g_DG : g.onLine DG := by euclid_finish
  have h_g_ne_d : g ≠ d := by euclid_finish
  have h_e_ne_g : e ≠ g := h_step3.1.2.2
  have h_tri_abc : formTriangle a b c AB BC AC := by
    exact ⟨⟨h_a_AB, h_b_AB, h_ab_ne⟩, h_b_BC, h_c_BC, h_c_AC, h_a_AC, h_AB_ne_BC, h_BC_ne_AC, h_AC_ne_AB⟩
  have h_tri_deg : formTriangle d e g DE EG DG := by euclid_finish
  euclid_apply (proposition_4 a b c d e g AB BC AC DE EG DG)
  euclid_finish

end Elements.Book1
