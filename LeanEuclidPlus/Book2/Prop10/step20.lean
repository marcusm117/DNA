import SystemE
import Book.Prop06
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.20: |BD| = |GD| [Prop.~1.6]. △BDG is isosceles: equal base angles ∠d:b:g = ∠d:g:b (step19) at
   b and g give equal opposite sides |d─b| = |d─g| (proposition_6 d b g AD EB FD). The formTriangle
   precondition is its own sub-node (step20_tri). No ∟/2 facts needed (only the step19 angle equality). -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step20
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD) (hab_b : b.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB) (hg_eb : g.onLine EB)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF) (hf_fd : f.onLine FD)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hstep19 : ∠ d:g:b = ∠ d:b:g) :
  |(b─d)| = |(g─d)| := by
  have step20_tri : formTriangle d b g AD EB FD := by sorry
  euclid_apply (proposition_6 d b g AD EB FD)
  euclid_finish

end Elements.Book2
