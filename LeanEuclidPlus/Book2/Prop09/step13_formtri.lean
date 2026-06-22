import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

set_option systemE.solverTime 30 in
-- step13 helper: formTriangle e g f CE FG EB. f ∉ CE (DF ∥ CE); the three sides are
-- pairwise distinct (witnessed by f off CE for CE≠FG,EB≠CE; e off FG for FG≠EB).
theorem helper_2_9_step13_formtri
  (a b c d e f g e0 e1 : Point) (AB CE DF EB FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE) (hce_g : g.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hbte : between c e e1)
  (hfg_f : f.onLine FG) (hfg_g : g.onLine FG)
  (hpar_df : ¬DF.intersectsLine CE)
  (hbegc : between e g c) :
  formTriangle e g f CE FG EB := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have hdoffCE : ¬(d.onLine CE) :=
    offLine_of_two_points d c e0 AB CE hab_d hab_c (by euclid_finish) hce_c hce_e0 hne0
  have hDFneCE : DF ≠ CE := fun h => hdoffCE (h ▸ hdf_d)
  have hfoffCE : ¬(f.onLine CE) :=
    offLine_of_parallel_simple f DF CE hdf_f hDFneCE hpar_df
  have heg : e ≠ g := by euclid_finish
  have heoffFG : ¬(e.onLine FG) :=
    offLine_of_two_points e g f CE FG heCE hce_g heg hfg_g hfg_f hfoffCE
  have hCEneFG : CE ≠ FG := fun h => hfoffCE (h ▸ hfg_f)
  have hEBneCE : EB ≠ CE := fun h => hfoffCE (h ▸ heb_f)
  have hFGneEB : FG ≠ EB := fun h => heoffFG (h ▸ heb_e)
  euclid_finish

end Elements.Book2
