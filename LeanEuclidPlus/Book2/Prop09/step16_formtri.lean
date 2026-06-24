import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- step16 helper: formTriangle b f d EB DF AB. f ∉ AB and e ∉ AB witness the pairwise
-- distinctness of the three sides.
theorem helper_2_9_step16_formtri
  (a b c d e f e0 e1 : Point) (AB CE DF EB : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hpar_df : ¬DF.intersectsLine CE)
  (hbefb : between e f b) :
  formTriangle b f d EB DF AB := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AB CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have hec : e ≠ c := by euclid_finish
  have heoAB : ¬(e.onLine AB) :=
    offLine_of_two_points e c a CE AB heCE hce_c hec hab_c hab_a haoffCE
  have hfb : f ≠ b := by euclid_finish
  have hfoffAB : ¬(f.onLine AB) :=
    offLine_of_two_points' f b e EB AB heb_f heb_b hfb hab_b heb_e heoAB
  have hdb : d ≠ b := by euclid_finish
  have hdoffDF : ¬(d.onLine EB) := by euclid_finish
  have hboffDF : ¬(b.onLine DF) := by euclid_finish
  have hEBneDF : EB ≠ DF := fun h => hboffDF (h ▸ heb_b)
  have hDFneAB : DF ≠ AB := fun h => hfoffAB (h ▸ hdf_f)
  have hABneEB : AB ≠ EB := fun h => heoAB (h ▸ heb_e)
  euclid_finish

end Elements.Book2
