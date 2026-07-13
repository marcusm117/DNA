import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hEc (a b c d e : Point) (AC DB : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (hb_off : ¬b.onLine AC)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB) (he_db : e.onLine DB)
    (hright : ∠ a:d:b = ∟) (hmid : |(a─d)| = |(d─c)|)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC) :
    |(e─a)| = |(e─c)| := by
  euclid_finish

end Elements.Book3
