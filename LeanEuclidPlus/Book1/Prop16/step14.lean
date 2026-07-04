import SystemE
import Book.Prop03
import Book.Prop10
import Book.Prop15
import Book.Prop04
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_16_step14 (a b c d g : Point) (AB BC AC : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_bcd : between b c d)
    (h_acg : between a c g)
    (h_g_AC : g.onLine AC) :
    ∠ a:c:d > ∠ a:b:c := by
  euclid_apply (proposition_10 b c BC) as e'
  euclid_apply (line_from_points a e') as AE'
  euclid_apply (extend_point_longer AE' a e' (a─e')) as h'
  euclid_apply (proposition_3 e' h' a e' AE' AE') as f'
  euclid_apply (line_from_points f' c) as FC'
  euclid_apply (proposition_15 b c a f' e' BC AE')
  euclid_apply (proposition_4 e' b a e' c f' BC AB AE' BC FC' AE')
  euclid_assert (∠ c:b:a = ∠ b:c:f')
  euclid_apply (proposition_15 a g b d c AC BC)
  euclid_finish

end Elements.Book1
