import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

set_option systemE.solverTime 30 in
theorem helper_2_9_step32_formtri
  (a b c e f e0 e1 : Point) (AB CE EA EB AF FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hea_e : e.onLine EA) (hea_a : a.onLine EA)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (haf_a : a.onLine AF) (haf_f : f.onLine AF)
  (hfg_f : f.onLine FG)
  (hpar_fg : ¬FG.intersectsLine AB)
  (hbefb : between e f b) :
  formTriangle e a f EA AF EB := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AB CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have heoffAB : ¬(e.onLine AB) :=
    offLine_of_two_points e c a CE AB heCE hce_c (by euclid_finish) hab_c hab_a haoffCE
  have haoffEB : ¬(a.onLine EB) :=
    offLine_of_two_points a b e AB EB hab_a hab_b (by euclid_finish) heb_b heb_e heoffAB
  have hfe : f ≠ e := by euclid_finish
  have hfoffEA : ¬(f.onLine EA) :=
    offLine_of_two_points f e a EB EA heb_f heb_e hfe hea_e hea_a haoffEB
  have hEAneAF : EA ≠ AF := fun h => hfoffEA (h ▸ haf_f)
  euclid_finish

end Elements.Book2
