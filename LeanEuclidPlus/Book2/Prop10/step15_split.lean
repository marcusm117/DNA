import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- step15 geometry: c's ray (ec) splits ∠AEB (a,c,b collinear, c between), so
-- ∠a:e:b = ∠a:e:c + ∠c:e:b. Pure geometry; needs c off EA and c off EB.
theorem helper_2_10_step15_split
  (a b c e e0 e1 : Point) (AD CE EA EB : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD)
  (hea_a : a.onLine EA) (hea_e : e.onLine EA)
  (heb_e : e.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD)
  (hacb : between a c b)
  (hbte : between c e e1) :
  ∠ a:e:b = ∠ a:e:c + ∠ c:e:b := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have hea : e ≠ a := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hce : c ≠ e := by euclid_finish
  have haoCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AD CE hab_a hab_c hca.symm hce_c hce_e0 hne0
  have heoAD : ¬(e.onLine AD) :=
    offLine_of_two_points e c a CE AD heCE hce_c hce.symm hab_c hab_a haoCE
  have hcofEA : ¬(c.onLine EA) :=
    offLine_of_two_points c a e AD EA hab_c hab_a hca hea_a hea_e heoAD
  have hcofEB : ¬(c.onLine EB) :=
    offLine_of_two_points c b e AD EB hab_c hab_b hcb heb_b heb_e heoAD
  euclid_finish

end Elements.Book2
