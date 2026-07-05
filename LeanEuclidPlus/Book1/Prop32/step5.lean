import SystemE
import Book.Prop29
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_32_step5
    (a b c d e : Point) (AB BC AC CE : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (ha_ne_b : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_ne_BC : AB ≠ BC) (hBC_ne_AC : BC ≠ AC) (hAC_ne_AB : AC ≠ AB)
    (hbcd : between b c d)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (hCE_noint_AB : ¬CE.intersectsLine AB)
    (he_side : e.sameSide a BC)
    (hAB_noint_CE : ¬AB.intersectsLine CE)
    (hdist_ac : distinctPointsOnLine a c AC)
    (hdist_bd : distinctPointsOnLine b d BC) :
    ∠ a:c:d = ∠ b:a:c + ∠ a:b:c := by
  euclid_apply (proposition_29''' b e a c AB CE AC)
  euclid_apply (proposition_29'''' e a d c b CE AB BC)
  euclid_finish

end Elements.Book1
