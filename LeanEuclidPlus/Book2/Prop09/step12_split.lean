import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

set_option systemE.solverTime 30 in
-- step12 geometry: c's ray (ec) splits ∠aeb (a,c,b collinear, c between) giving
-- ∠a:e:b = ∠a:e:c + ∠c:e:b, plus symmetry ∠a:e:c = ∠c:e:a. Pure geometry, NO ∟/2.
theorem helper_2_9_step12_split
  (a b c e e0 e1 : Point) (AB CE EA EB : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB)
  (hea_a : a.onLine EA) (hea_e : e.onLine EA)
  (heb_e : e.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1) :
  (∠ a:e:b = ∠ a:e:c + ∠ c:e:b) ∧ (∠ a:e:c = ∠ c:e:a) := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have hea : e ≠ a := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hce : c ≠ e := by euclid_finish
  have haoCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AB CE hab_a hab_c hca.symm hce_c hce_e0 hne0
  have heoAB : ¬(e.onLine AB) :=
    offLine_of_two_points e c a CE AB heCE hce_c hce.symm hab_c hab_a haoCE
  have hcofEA : ¬(c.onLine EA) :=
    offLine_of_two_points c a e AB EA hab_c hab_a hca hea_a hea_e heoAB
  have hcofEB : ¬(c.onLine EB) :=
    offLine_of_two_points c b e AB EB hab_c hab_b hcb heb_b heb_e heoAB
  refine ⟨?_, angle_symm a e c ⟨hea.symm, hce.symm⟩⟩
  euclid_finish

end Elements.Book2
