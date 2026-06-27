import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.21: ∠FEG = ∟/2. △EFG: the angle at F is ∟ (= opposite angle at C, [Prop.~1.34], sub-node
   step21_fright), EGF = ∟/2 (sub-node step21_egf, since ∠e:g:f = ∠d:g:b = ∟/2 from step18), and the
   three angles sum to ∟+∟ (sub-node step21_sum), so the remaining ∠f:e:g = ∟/2. formParallelogram
   CEFD is sub-node step21_pgram. linarith combines (no euclid_finish touches the ∟/2 facts). -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step21
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (hg_eb : g.onLine EB) (he_eb : e.onLine EB) (hb_eb : b.onLine EB)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hright : ∠ a:c:e = ∟)
  (hstep18 : ∠ d:g:b = ∟ / 2) :
  ∠ f:e:g = ∟ / 2 := by
  have step21_pgram : formParallelogram c e d f CE FD AD EF := by sorry
  have step21_fright : ∠ e:f:g = ∟ := by sorry
  have step21_sum : ∠ f:e:g + ∠ e:f:g + ∠ e:g:f = ∟ + ∟ := by sorry
  have step21_egf : ∠ e:g:f = ∟ / 2 := by sorry
  linarith [step21_fright, step21_sum, step21_egf]

end Elements.Book2
