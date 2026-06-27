import SystemE
import Book.Prop29
import Helpers.OffLine
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

-- step6 (2.10.6): EF crosses the parallels CE and FD at the feet e (on CE) and f (on FD),
-- so the co-interior angles ∠CEF and ∠EFD sum to two right-angles (proposition_29''''').
-- Preconditions: e off AD (so EF≠AD, c.sameSide d EF via the parallel witness e) and CE∥FD.
set_option systemE.solverTime 30 in
theorem helper_2_10_step6
  (a b c d e e0 e1 f : Point) (AD CE EF FD : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD)
  (hbte : between c e e1)
  (hEF_e : e.onLine EF) (hEF_f : f.onLine EF) (hEFAD : ¬EF.intersectsLine AD)
  (hFD_d : d.onLine FD) (hFD_f : f.onLine FD) (hFDCE : ¬FD.intersectsLine CE) :
  ∠ c:e:f + ∠ e:f:d = ∟ + ∟ := by
  have heCE : e.onLine CE := by euclid_apply (between_same_line_in c e e1 CE); assumption
  have hec : e ≠ c := by euclid_finish
  have heoff : ¬(e.onLine AD) :=
    offLine_of_two_points' e c e0 CE AD heCE hce_c hec hab_c hce_e0 hne0
  have hss : c.sameSide d EF :=
    sameSide_of_parallel c d e AD EF hab_c hab_d hEF_e heoff hEFAD
  have hCEFD : ¬(CE.intersectsLine FD) := fun h => hFDCE (intersection_symm CE FD h)
  have hef : e ≠ f := by euclid_finish
  have hfd : f ≠ d := by euclid_finish
  euclid_apply (proposition_29''''' c d e f CE FD EF)
  euclid_finish

end Elements.Book2
