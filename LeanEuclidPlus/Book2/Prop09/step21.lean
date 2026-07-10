import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

theorem helper_2_9_step21
  (a b c e e0 e1 : Point) (AB CE EA : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hea_e : e.onLine EA) (hea_a : a.onLine EA)
  (hstep1 : ∠ a:c:e = ∟) :
  |(e─a)| * |(e─a)| = |(a─c)| * |(a─c)| + |(c─e)| * |(c─e)| := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AB CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have heoffAB : ¬(e.onLine AB) :=
    offLine_of_two_points e c a CE AB heCE hce_c (by euclid_finish) hab_c hab_a haoffCE
  have hformtri : formTriangle c a e AB EA CE := by euclid_finish
  euclid_apply (proposition_47 c a e AB EA CE)
  euclid_finish

end Elements.Book2
