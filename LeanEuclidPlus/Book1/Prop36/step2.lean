import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_36_step2 (e f g h : Point) (AH BG EF HG : Line)
  (h_e_AH : e.onLine AH) (h_h_AH : h.onLine AH)
  (h_f_BG : f.onLine BG) (h_g_BG : g.onLine BG)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
  (h_h_HG : h.onLine HG) (h_g_HG : g.onLine HG) (h_h_ne_g : h ≠ g)
  (h_ss : e.sameSide f HG)
  (h_par1 : ¬AH.intersectsLine BG)
  (h_par2 : ¬EF.intersectsLine HG)
  (hassump1 : |(b─c)| = |(f─g)|)
  (hassump2 : |(f─g)| = |(e─h)|) :
  |(b─c)| = |(e─h)| := by
  have step2_assumption2 : |(f─g)| = |(e─h)| := by sorry
  exact hassump1.trans step2_assumption2

end Elements.Book1
