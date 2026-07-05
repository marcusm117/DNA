import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_32_step3
    (a b c d e : Point) (AB BC AC CE : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (ha_ne_b : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hbcd : between b c d)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (hCE_noint_AB : ¬CE.intersectsLine AB)
    (he_side : e.sameSide a BC)
    (hassump1 : ¬(AB.intersectsLine CE))
    (hassump2 : distinctPointsOnLine b d BC) :
    ∠ e:c:d = ∠ a:b:c := by
  euclid_apply (proposition_29'''' e a d c b CE AB BC)
  euclid_finish

end Elements.Book1
