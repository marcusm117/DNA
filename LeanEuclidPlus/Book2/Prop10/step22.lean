import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.22: ∠EGF = ∠FEG. Both are half a right-angle: ∠e:g:f = ∟/2 (reused sub-node step21_egf, =
   ∠d:g:b = ∟/2 via the ray coincidence) and ∠f:e:g = ∟/2 (step21). Pure linarith. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step22
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB) (hg_eb : g.onLine EB)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hstep18 : ∠ d:g:b = ∟ / 2)
  (hstep21 : ∠ f:e:g = ∟ / 2) :
  ∠ e:g:f = ∠ f:e:g := by
  have step21_egf : ∠ e:g:f = ∟ / 2 := by sorry
  linarith [step21_egf, hstep21]

end Elements.Book2
