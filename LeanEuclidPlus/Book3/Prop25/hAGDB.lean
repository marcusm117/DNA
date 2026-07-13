import SystemE
import Book1.Prop32.Main
import Book1Variants.Prop29

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hAGDB (a b c d g : Point) (AC DB AB AG : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (hb_off : ¬b.onLine AC)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (ha_ag : a.onLine AG) (hg_ag : g.onLine AG) (hg_ne : g ≠ a)
    (hside : g.onLine AB ∨ g.sameSide d AB)
    (hang : ∠ g:a:b = ∠ a:b:d) (hright : ∠ a:d:b = ∟)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (hmid : |(a─d)| = |(d─c)|) (hapex : |(a─b)| = |(c─b)|) :
    AG.intersectsLine DB := by
  by_contra hpar
  -- triangle abd angle sum: ∠bad + ∠abd = ∟ (since ∠adb = ∟)
  euclid_apply (proposition_32 b a d c AB AC DB)
  -- AG ∥ DB (by hpar), transversal AC: alternate angle ∠g:a:d = ∠a:d:b = ∟
  euclid_apply (proposition_29''' g b a d AG DB AC)
  euclid_finish

end Elements.Book3
