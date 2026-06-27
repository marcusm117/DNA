import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop10.step21_egf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.22: ∠EGF = ∠FEG. Both are half a right-angle: ∠e:g:f = ∟/2 (reused sub-node step21_egf, =
   ∠d:g:b = ∟/2 via the ray coincidence) and ∠f:e:g = ∟/2 (step21). Pure linarith. -/
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
  have step21_egf : ∠ e:g:f = ∟ / 2 := by euclid_apply (helper_2_10_step21_egf a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ d:g:b = ∟ / 2; assumption)))
  linarith [step21_egf, hstep21]

end Elements.Book2
