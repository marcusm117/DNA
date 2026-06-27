import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.21 sub: the angle at F (∠e:f:g) is a right-angle. It equals the opposite angle ∠ECD at C
   [Prop.~1.34] (parallelogram diagonal ED built locally for proposition_34's precondition); ∠ECD = ∟
   since CE ⊥ AD. The full figure context lets euclid_finish place g and close the right-angle goal. -/
theorem helper_2_10_step21_fright
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (hg_eb : g.onLine EB) (he_eb : e.onLine EB) (hb_eb : b.onLine EB)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hpgram : formParallelogram c e d f CE FD AD EF)
  (hright : ∠ a:c:e = ∟) :
  ∠ e:f:g = ∟ := by
  euclid_apply (line_from_points e d) as ED
  euclid_apply (proposition_34 c e d f CE FD AD EF ED)
  euclid_finish

end Elements.Book2
