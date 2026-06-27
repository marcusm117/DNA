import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.21 sub: ∠EGF = ∟/2. The ray g→e coincides with g→b (e, b, g on EB, b between) and the ray
   g→f coincides with g→d (f, d, g on FD, d between), so ∠e:g:f = ∠d:g:b = ∟/2 (step18). The ∟/2 hyp
   is cleared for the pure ray-equality euclid_finish, then linarith halves. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step21_egf
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB) (hg_eb : g.onLine EB)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hstep18 : ∠ d:g:b = ∟ / 2) :
  ∠ e:g:f = ∟ / 2 := by
  have hray : ∠ e:g:f = ∠ d:g:b := by clear hstep18; euclid_finish
  linarith [hray, hstep18]

end Elements.Book2
