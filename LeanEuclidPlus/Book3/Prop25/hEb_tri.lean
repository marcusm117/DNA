import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hEb_tri (a b c d e g3 : Point) (AC AG3 AB DB : Line)
    (ha_ag3 : a.onLine AG3) (he_ag3 : e.onLine AG3) (hg3_ag3 : g3.onLine AG3) (hg3_ne : g3 ≠ a)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (hb_db : b.onLine DB) (he_db : e.onLine DB)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (hd_db : d.onLine DB) (hb_off : ¬b.onLine AC)
    (hside : g3.onLine AB ∨ g3.sameSide d AB)
    (hang : ∠ g3:a:b = ∠ a:b:d) (hlt : ∠ a:b:d < ∠ b:a:d) :
    formTriangle e a b AG3 AB DB := by
  rcases hside with hon | hss
  · exfalso; euclid_finish
  · euclid_finish

end Elements.Book3
