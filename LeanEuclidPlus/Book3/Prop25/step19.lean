import SystemE
import Book1.Prop06.Main

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step19 (a b c d : Point) (AC AB DB : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c) (hb_off : ¬b.onLine AC)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB)
    (hassump1 : ∠ a:b:d = ∠ b:a:d)
    (hassump2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|) :
    |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| := by
  euclid_apply (proposition_6 d a b AC AB DB)
  euclid_finish

end Elements.Book3
