import SystemE
import Book.Prop15
import Mathlib.Tactic.Linarith
import Book2.Prop10.step16_beg
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.16: ∠DBG = ∟/2. Vertical angles at b (EB × AD): ∠e:b:c = ∠d:b:g (proposition_15), then
   ∠d:b:g = ∠e:b:c = ∟/2. proposition_15 needs `between e b g` (b = EB ∩ AD, e above / g below AD)
   — the step16_beg sub-node. KEEP ∟/2 OUT OF THE SMT: prove the pure vertical equality with the
   ∟/2 half-angle hyp CLEARED (it crashes the SMT translator), then combine via linarith. -/
theorem helper_2_10_step16
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD) (hab_b : b.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB) (hg_eb : g.onLine EB)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF) (hf_fd : f.onLine FD)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hhalf : ∠ e:b:c = ∟ / 2) :
  ∠ d:b:g = ∟ / 2 := by
  have step16_beg : between e b g := by euclid_apply (helper_2_10_step16_beg a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)))
  have hvert : ∠ e:b:c = ∠ d:b:g := by
    clear hhalf
    euclid_apply (proposition_15 e g c d b EB AD)
    euclid_finish
  linarith [hhalf, hvert]

end Elements.Book2
