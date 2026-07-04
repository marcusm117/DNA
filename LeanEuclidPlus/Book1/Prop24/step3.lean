import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_24_step3
  (d e g f : Point) (DE EF DF DG EG FG : Line)
  (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_de_ne : d ≠ e)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
  (h_f_DF : f.onLine DF) (h_d_DF : d.onLine DF)
  (h_DE_ne_EF : DE ≠ EF) (h_EF_ne_DF : EF ≠ DF) (h_DF_ne_DE : DF ≠ DE)
  (h_d_DG : d.onLine DG) (h_g''_DG : g''.onLine DG) (h_between_g : between d g g'')
  (h_e_EG : e.onLine EG) (h_g_EG : g.onLine EG)
  (h_f_FG : f.onLine FG) (h_g_FG : g.onLine FG)
  (h_step1 : ∠ e:d:g = ∠ b:a:c) (h_bac_gt : ∠ b:a:c > ∠ e:d:f)
  : distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG := by
  have h_g_DG : g.onLine DG := by euclid_finish
  have h_g_ne_d : g ≠ d := by euclid_finish
  have h_e_ne_g : e ≠ g := by euclid_finish
  have h_f_ne_g : f ≠ g := by euclid_finish
  exact ⟨⟨h_e_EG, h_g_EG, h_e_ne_g⟩, ⟨h_f_FG, h_g_FG, h_f_ne_g⟩⟩

end Elements.Book1
