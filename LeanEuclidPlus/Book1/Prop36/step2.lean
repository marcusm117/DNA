import SystemE
import Book1.Prop36.step2_assumption2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

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
  have step2_assumption2 : |(f─g)| = |(e─h)| := by euclid_apply (helper_1_36_step2_assumption2 e f g h AH BG EF HG (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show f.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine HG; assumption)) (by euclid_assumption "" (show g.onLine HG; assumption)) (by euclid_assumption "" (show h ≠ g; assumption)) (by euclid_assumption "" (show e.sameSide f HG; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine HG; assumption)))
  exact hassump1.trans step2_assumption2

end Elements.Book1
