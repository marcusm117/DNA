import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step3 (a b : Point) (AC AB : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (ha_ac : a.onLine AC) (hb_off : ¬b.onLine AC) :
    distinctPointsOnLine a b AB := by
  euclid_finish

end Elements.Book3
