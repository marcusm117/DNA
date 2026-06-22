import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

set_option systemE.solverTime 30 in
-- step13 helper: f.sameSide b CE. f lies between e,b on EB (between e f b), e ∈ CE, and
-- f ∉ CE (DF ∥ CE), so pasch_2 gives f.sameSide b CE.
theorem helper_2_9_step13_fsb
  (a b c d e f e0 e1 : Point) (AB CE DF EB : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hbte : between c e e1)
  (hpar : ¬DF.intersectsLine CE)
  (hbefb : between e f b) :
  f.sameSide b CE := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have hdoffCE : ¬(d.onLine CE) :=
    offLine_of_two_points d c e0 AB CE hab_d hab_c (by euclid_finish) hce_c hce_e0 hne0
  have hDFneCE : DF ≠ CE := fun h => hdoffCE (h ▸ hdf_d)
  have hfoffCE : ¬(f.onLine CE) :=
    offLine_of_parallel_simple f DF CE hdf_f hDFneCE hpar
  euclid_apply (pasch_2 e f b CE)
  euclid_finish

end Elements.Book2
