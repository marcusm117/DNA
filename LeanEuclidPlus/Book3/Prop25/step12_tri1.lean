import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12_tri1 (a c d e : Point) (AC AG DB : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (ha_ag : a.onLine AG) (he_ag : e.onLine AG)
    (hd_db : d.onLine DB) (he_db : e.onLine DB)
    (heoff : ¬ e.onLine AC) :
    formTriangle d a e AC AG DB := by
  euclid_finish

end Elements.Book3
