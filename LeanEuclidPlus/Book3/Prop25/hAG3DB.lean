import SystemE
import Book1.Prop32.Main
import Book1Variants.Prop29

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hAG3DB (a b c d g3 : Point) (AC DB AB AG3 : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (hb_off : ¬b.onLine AC)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (ha_ag3 : a.onLine AG3) (hg3_ag3 : g3.onLine AG3) (hg3_ne : g3 ≠ a)
    (hside : g3.onLine AB ∨ g3.sameSide d AB)
    (hang : ∠ g3:a:b = ∠ a:b:d) (hright : ∠ a:d:b = ∟)
    (hngt : ¬ ∠ a:b:d > ∠ b:a:d) (hneq : ¬ ∠ a:b:d = ∠ b:a:d) :
    AG3.intersectsLine DB := by
  by_contra hpar
  rcases hside with hon | hss
  · euclid_finish
  · euclid_apply (proposition_32 b a d c AB AC DB)
    have hg3s : g3.sameSide b AC := by euclid_finish
    euclid_apply (proposition_29''''' g3 b a d AG3 DB AC)
    euclid_finish

end Elements.Book3
