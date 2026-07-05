import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_32_step7
    (a b c d : Point) (AB BC AC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (ha_ne_b : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_ne_BC : AB ≠ BC) (hBC_ne_AC : BC ≠ AC) (hAC_ne_AB : AC ≠ AB)
    (hstep6 : ∠ a:c:d + ∠ a:c:b = ∠ b:a:c + ∠ a:b:c + ∠ a:c:b) :
    ∠ a:c:d + ∠ a:c:b = ∠ a:b:c + ∠ b:c:a + ∠ c:a:b := by
  euclid_finish

end Elements.Book1
