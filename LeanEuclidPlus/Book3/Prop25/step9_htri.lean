import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step9_htri (a b c d e g : Point) (AC AG AB DB : Line)
    (ha_ag : a.onLine AG) (he_ag : e.onLine AG) (hg_ag : g.onLine AG) (hg_ne : g ≠ a)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (hb_db : b.onLine DB) (he_db : e.onLine DB)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (hd_db : d.onLine DB) (hb_off : ¬b.onLine AC)
    (hside : g.onLine AB ∨ g.sameSide d AB)
    (hang : ∠ g:a:b = ∠ a:b:d) (hgt : ∠ a:b:d > ∠ b:a:d) :
    formTriangle e a b AG AB DB := by
  rcases hside with hon | hss
  · exfalso; euclid_finish
  · euclid_finish

end Elements.Book3
