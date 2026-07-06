import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step34
    (a b c h : Point) (AB BC AC AH : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB)
    (ha_AH : a.onLine AH) (hh_AH : h.onLine AH)
    (hbetween : between b h c)
    (hstep33 : ∠ b:h:a = ∠ b:c:a) : False := by
  euclid_apply (proposition_16 a c h b AC BC AH)
  euclid_finish

end Elements.Book1
