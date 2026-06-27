import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.17: ∠BDG = ∟. It equals ∠DCE (alternate angles [Prop.~1.29]: FD ∥ CE cut by transversal AD),
   and ∠DCE = ∟ since CE ⊥ AD. proposition_29''' g e d c FD CE AD gives ∠g:d:c = ∠d:c:e; b,c are on
   the same ray from d on AD so ∠b:d:g = ∠g:d:c, hence ∠b:d:g = ∠d:c:e = ∟. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step17
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD) (hab_b : b.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hbte0 : between c e0 e1) (hbte : between c e e1)
  (hne0 : ¬e0.onLine AD) (hperp : ∠ a:c:e0 = ∟)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB) (hg_eb : g.onLine EB)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF) (hf_fd : f.onLine FD)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hright : ∠ a:c:e = ∟) :
  ∠ b:d:g = ∟ := by
  have heCE : e.onLine CE := by euclid_apply (between_same_line_in c e e1 CE); assumption
  euclid_apply (proposition_29''' g e d c FD CE AD)
  euclid_finish

end Elements.Book2
