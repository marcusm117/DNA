import SystemE
import Book.Prop38
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step7 (a b c e : Point) (AB BC AC AE AG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_AB_ne_BC : AB ≠ BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE)
    (h_a_AG : a.onLine AG) (h_par : ¬(AG.intersectsLine BC))
    (h_bet : between b e c)
    (hassump1 : |(b─e)| = |(e─c)|)
    (hassump2 : |(b─e)| = |(e─c)|)
    (hassump3 : ¬(AG.intersectsLine BC)) :
    Triangle.area △ a:b:e = Triangle.area △ a:e:c := by
  euclid_apply (proposition_38 a b e a e c AG BC AB AE AE AC)
  euclid_finish

end Elements.Book1
