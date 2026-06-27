import SystemE
import Book.Prop47
import Helpers.OffLine
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.36: square on AG = squares on AE + EG [Prop.~1.47]. △AEG is right-angled at E (∠a:e:g = ∟ =
   ∠a:e:b since g is on the ray e→b, and ∠a:e:b = ∟ by step15), so proposition_47 gives |a─g|² =
   |a─e|² + |e─g|². The triangle side EG is local (line_from_points e g). -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step36
  (a b c d e e0 e1 f g : Point) (AD CE EA EB EF FD AG : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (hea_e : e.onLine EA) (hea_a : a.onLine EA)
  (hag_a : a.onLine AG) (hag_g : g.onLine AG)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB) (hg_eb : g.onLine EB)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF) (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (hstep15 : ∠ a:e:b = ∟) :
  |(a─g)| * |(a─g)| = |(a─e)| * |(a─e)| + |(e─g)| * |(e─g)| := by
  euclid_apply (line_from_points e g) as EG
  euclid_apply (proposition_47 e a g EA AG EG)
  linarith

end Elements.Book2
