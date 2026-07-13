import SystemE
import Book1.Prop32.Main

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hEb_ang (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (hb_off : ¬b.onLine AC)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB) (he_db : e.onLine DB)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (ha_ag3 : a.onLine AG3) (hg3_ag3 : g3.onLine AG3) (he_ag3 : e.onLine AG3) (hg3_ne : g3 ≠ a)
    (hside : g3.onLine AB ∨ g3.sameSide d AB)
    (hang : ∠ g3:a:b = ∠ a:b:d) (hright : ∠ a:d:b = ∟)
    (hlt : ∠ a:b:d < ∠ b:a:d)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC) :
    ∠ a:b:e = ∠ b:a:e := by
  rcases hside with hon | hss
  · exfalso; euclid_finish
  · euclid_apply (proposition_32 b a d c AB AC DB)
    have hg3s : g3.sameSide b AC := by euclid_finish
    have hnbtw : ¬ between e a g3 := by euclid_finish
    have hbed : between b e d := by euclid_finish
    euclid_finish

end Elements.Book3
