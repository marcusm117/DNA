import SystemE
import Book.Prop13
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_32_step8
    (a b c d : Point) (AB BC AC : Line)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hBC_ne_AC : BC ≠ AC)
    (hbcd : between b c d)
    (hdist_ac : distinctPointsOnLine a c AC)
    (hdist_bd : distinctPointsOnLine b d BC) :
    ∠ a:c:d + ∠ a:c:b = ∟ + ∟ := by
  euclid_apply (proposition_13 a c d b AC BC)
  euclid_finish

end Elements.Book1
