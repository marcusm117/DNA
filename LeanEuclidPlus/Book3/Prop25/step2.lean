import SystemE
import Book1.Prop11.Main

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step2 (a b c d : Point) (AC DB : Line)
    (hac : a.onLine AC) (hcc : c.onLine AC) (hac_ne : a ≠ c)
    (hb_off : ¬b.onLine AC) (hapex : |(a─b)| = |(c─b)|)
    (hbet : between a d c) (hmid : |(a─d)| = |(d─c)|)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB) :
    ∠ a:d:b = ∟ := by
  -- [1.11]: erect the perpendicular to AC at the midpoint d; b (the apex, |ab|=|cb|)
  -- lies on it, so DB coincides with that perpendicular and ∠a:d:b = ∟.
  euclid_apply (proposition_11 a c d AC)
  euclid_finish

end Elements.Book3
