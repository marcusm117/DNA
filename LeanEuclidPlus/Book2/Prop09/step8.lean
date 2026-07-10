import SystemE
import Book1.Prop32.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

-- step8 (2.9.8): the remaining angles EAC + AEC of △AEC sum to one right-angle
-- (the third angle ACE is right). proposition_32 (triangle angle-sum); d=b is the
-- point beyond C on line AC (between a c b). Off-line facts give formTriangle.
theorem helper_2_9_step8
  (a b c e e0 e1 : Point) (AB EA CE : Line)
  (hab_a : a.onLine AB) (hab_c : c.onLine AB)
  (hea_a : a.onLine EA) (hea_e : e.onLine EA)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hstep1 : ∠ a:c:e = ∟) :
  ∠ e:a:c + ∠ a:e:c = ∟ := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AB CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have heoffAB : ¬(e.onLine AB) :=
    offLine_of_two_points e c a CE AB heCE hce_c (by euclid_finish) hab_c hab_a haoffCE
  have hCEneAB : CE ≠ AB := fun h => hne0 (h ▸ hce_e0)
  have hformTri : formTriangle e a c EA AB CE := by euclid_finish
  have hsum : ∠ e:a:c + ∠ a:c:e + ∠ c:e:a = ∟ + ∟ := by
    euclid_apply (proposition_32 e a c b EA AB CE)
    euclid_finish
  euclid_finish

end Elements.Book2
