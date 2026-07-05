import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_36_step2_assumption2 (e f g h : Point) (AH BG EF HG : Line)
  (h_e_AH : e.onLine AH) (h_h_AH : h.onLine AH)
  (h_f_BG : f.onLine BG) (h_g_BG : g.onLine BG)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
  (h_h_HG : h.onLine HG) (h_g_HG : g.onLine HG) (h_h_ne_g : h ≠ g)
  (h_ss : e.sameSide f HG)
  (h_par1 : ¬AH.intersectsLine BG)
  (h_par2 : ¬EF.intersectsLine HG) :
  |(f─g)| = |(e─h)| := by
  have h_pgram : formParallelogram e h f g AH BG EF HG :=
    ⟨h_e_AH, h_h_AH, h_f_BG, h_g_BG, h_e_EF, h_f_EF, ⟨h_h_HG, h_g_HG, h_h_ne_g⟩, h_ss, h_par1, h_par2⟩
  euclid_apply (proposition_34' e h f g AH BG EF HG)
  euclid_finish

end Elements.Book1
