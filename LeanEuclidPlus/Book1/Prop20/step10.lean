import SystemE
import Book.Prop03
import Book.Prop05
import Book.Prop19
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_20_step10 (a b c : Point) (AB BC AC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_aAC : a.onLine AC) (h_cAC : c.onLine AC)
    (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_aneb : a ≠ b) :
    |(b─c)| + |(c─a)| > |(a─b)| := by
  euclid_apply (extend_point_longer AC a c (c─b)) as f'
  euclid_apply (proposition_3 c f' c b AC BC) as f
  euclid_apply (line_from_points f b) as FB
  euclid_apply (proposition_5' c b f BC FB AC)
  euclid_apply (sum_angles_onlyif b a f c AB FB)
  euclid_apply (proposition_19 a b f AB FB AC)
  euclid_finish

end Elements.Book1
