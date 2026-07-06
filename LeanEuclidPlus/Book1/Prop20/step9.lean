import SystemE
import Book1.Prop03.Main
import Book1.Prop05.variants
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9 (a b c : Point) (AB BC AC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_aAC : a.onLine AC) (h_cAC : c.onLine AC)
    (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_aneb : a ≠ b) :
    |(a─b)| + |(b─c)| > |(a─c)| := by
  euclid_apply (extend_point_longer BC c b (b─a)) as e'
  euclid_apply (proposition_3 b e' b a BC AB) as e
  euclid_apply (line_from_points e a) as EA
  euclid_apply (proposition_5' b a e AB EA BC)
  euclid_apply (sum_angles_onlyif a c e b AC EA)
  euclid_apply (proposition_19 c a e AC EA BC)
  euclid_finish

end Elements.Book1
