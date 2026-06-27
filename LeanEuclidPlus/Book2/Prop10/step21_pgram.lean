import SystemE
import Helpers.OffLine
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

/- 2.10.21 sub: CEFD is a parallelogram (CE ∥ FD, EF ∥ CD=AD), with the right-angle corner at C —
   the formParallelogram precondition of proposition_34 (angle-at-F = angle-at-C). -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step21_pgram
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE) :
  formParallelogram c e d f CE FD AD EF := by
  have heCE : e.onLine CE := by euclid_apply (between_same_line_in c e e1 CE); assumption
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AD CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have heoffAD : ¬(e.onLine AD) :=
    offLine_of_two_points e c a CE AD heCE hce_c (by euclid_finish) hab_c hab_a haoffCE
  have hCEneFD : ¬(CE.intersectsLine FD) := fun h => hFDCE (intersection_symm CE FD h)
  have hADneEF : ¬(AD.intersectsLine EF) := fun h => hEFAD (intersection_symm AD EF h)
  euclid_finish

end Elements.Book2
