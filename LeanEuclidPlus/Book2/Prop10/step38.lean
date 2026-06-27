import SystemE
import Book.Prop47
import Helpers.OffLine
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.38: squares on AD + DG = square on AG [Prop.~1.47]. △ADG is right-angled at D (∠a:d:g = ∟; FD ⊥
   AD, so the angle at d between da = AD and dg = FD is right — cf. step17 ∠b:d:g = ∟), so proposition_47
   gives |a─g|² = |a─d|² + |d─g|². All three lines (AD, AG, FD) are constructed. linarith flips it. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step38
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD AG : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (hag_a : a.onLine AG) (hag_g : g.onLine AG)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (hg_eb : g.onLine EB) (he_eb : e.onLine EB) (hb_eb : b.onLine EB)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hstep17 : ∠ b:d:g = ∟) :
  |(a─d)| * |(a─d)| + |(d─g)| * |(d─g)| = |(a─g)| * |(a─g)| := by
  euclid_apply (proposition_47 d a g AD AG FD)
  linarith

end Elements.Book2
