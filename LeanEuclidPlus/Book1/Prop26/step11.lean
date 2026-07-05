import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step11
    (a b c g : Point) (AB BC AC GC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB)
    (hg_GC : g.onLine GC) (hc_GC : c.onLine GC)
    (hbetween : between b g a)
    (hstep10 : ∠ b:c:g = ∠ b:c:a) : False := by
  euclid_finish

end Elements.Book1
