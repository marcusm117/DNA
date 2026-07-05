import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step4
    (a b c d e f g : Point) (AB BC AC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB)
    (hbetween : between b g a)
    (hang1 : ∠ a:b:c = ∠ d:e:f) :
    ∠ g:b:c = ∠ d:e:f := by
  have hg_AB : g.onLine AB := by euclid_finish
  have hgb : g ≠ b := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have h : ∠ g:b:c = ∠ a:b:c := by
    euclid_apply (equal_angles b g a c c AB BC)
    euclid_finish
  exact h.trans hang1

end Elements.Book1
