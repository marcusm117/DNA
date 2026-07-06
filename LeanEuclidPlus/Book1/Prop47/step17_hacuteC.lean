import SystemE
import Book.Prop17
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_hacuteC
    (a b c : Point) (AB BC AC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (h_bac : (∠ b:a:c : ℝ) = ∟) :
    (∠ a:c:b : ℝ) < ∟ := by
  euclid_apply (proposition_17 b c a BC AC AB)
  euclid_finish

end Elements.Book1
