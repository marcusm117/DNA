import SystemE
import Book.Prop47
import Helpers.OffLine
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.26: square on EA = squares on EC + CA [Prop.~1.47]. △ECA is right-angled at C (∠a:c:e = ∟,
   step1), so proposition_47 (Pythagoras) gives |e─a|² = |e─c|² + |c─a|². formTriangle ECA + the right
   angle discharge from the figure context. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step26
  (a b c d e e0 e1 f g : Point) (AD CE EA EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (hea_e : e.onLine EA) (hea_a : a.onLine EA)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hright : ∠ a:c:e = ∟) :
  |(e─a)| * |(e─a)| = |(e─c)| * |(e─c)| + |(c─a)| * |(c─a)| := by
  euclid_apply (proposition_47 c e a CE EA AD)
  linarith

end Elements.Book2
