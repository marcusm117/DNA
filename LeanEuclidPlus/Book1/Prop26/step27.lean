import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step27
    (a b c d e f h : Point) (AB BC AC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB)
    (hbetween : between b h c)
    (hang1 : ∠ a:b:c = ∠ d:e:f) :
    ∠ a:b:h = ∠ d:e:f := by
  have hh_BC : h.onLine BC := by euclid_finish
  have hbh : b ≠ h := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have heq : ∠ a:b:h = ∠ a:b:c := by
    euclid_apply (equal_angles b a a h c AB BC)
    euclid_finish
  exact heq.trans hang1

end Elements.Book1
