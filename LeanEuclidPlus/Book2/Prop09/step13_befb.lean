import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- step13 root betweenness: f (= DF ∩ EB) lies between e and b on EB.
-- e,b are on opposite sides of DF (e sameSide c across DF since CE∥DF; c,b opposite
-- across DF via pasch_3 on between c d b with d ∈ DF); then pasch_4.
theorem helper_2_9_step13_befb
  (b c d e e0 e1 f : Point) (AB CE DF EB : Line)
  (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_b : b.onLine EB) (heb_f : f.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hbte : between c e e1)
  (hpar : ¬DF.intersectsLine CE) :
  between e f b := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have hdoffCE : ¬(d.onLine CE) :=
    offLine_of_two_points d c e0 AB CE hab_d hab_c (by euclid_finish) hce_c hce_e0 hne0
  have hCEneDF : CE ≠ DF := fun h => hdoffCE (h ▸ hdf_d)
  have hnCEiDF : ¬CE.intersectsLine DF := fun h => hpar (intersection_symm CE DF h)
  have hecDF : e.sameSide c DF :=
    sameSide_of_parallel_both e c CE DF heCE hce_c hCEneDF hnCEiDF
  have hncbDF : ¬(c.sameSide b DF) := by
    euclid_apply (pasch_3 c d b DF)
    assumption
  have hnebDF : ¬(e.sameSide b DF) := by
    intro h
    apply hncbDF
    exact same_side_symm b c DF (same_side_trans e b c DF ⟨h, hecDF⟩)
  euclid_apply (pasch_4 e f b DF EB)
  euclid_finish

end Elements.Book2
