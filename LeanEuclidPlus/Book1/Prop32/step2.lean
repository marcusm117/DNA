import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_32_step2
    (a b c e : Point) (AB BC AC CE : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (ha_ne_b : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAC_ne_AB : AC ≠ AB)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (hCE_noint_AB : ¬CE.intersectsLine AB)
    (he_side : e.sameSide a BC)
    (hassump1 : ¬(AB.intersectsLine CE))
    (hassump2 : distinctPointsOnLine a c AC) :
    ∠ b:a:c = ∠ a:c:e := by
  euclid_apply (proposition_29''' b e a c AB CE AC)
  euclid_finish

end Elements.Book1
