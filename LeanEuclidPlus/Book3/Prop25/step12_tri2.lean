import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12_tri2 (a c d e : Point) (AC EC DB : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (hc_ec : c.onLine EC) (he_ec : e.onLine EC)
    (hd_db : d.onLine DB) (he_db : e.onLine DB)
    (heoff : ¬ e.onLine AC) :
    formTriangle d c e AC EC DB := by
  euclid_finish

end Elements.Book3
