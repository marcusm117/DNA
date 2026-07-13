import SystemE
import Book1.Prop32.Main

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step9_assumption1 (a b c d e g : Point) (AC DB AB AG : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (hb_off : ¬b.onLine AC)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB) (he_db : e.onLine DB)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (ha_ag : a.onLine AG) (hg_ag : g.onLine AG) (he_ag : e.onLine AG) (hg_ne : g ≠ a)
    (hside : g.onLine AB ∨ g.sameSide d AB)
    (hang : ∠ g:a:b = ∠ a:b:d) (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a) (hright : ∠ a:d:b = ∟)
    (hgt : ∠ a:b:d > ∠ b:a:d) :
    ∠ a:b:e = ∠ b:a:e := by
  obtain ⟨hbae, hne⟩ := hstep6
  -- e lies on the far side of AC from b (the ray a→g crosses AC-perpendicular DB beyond d),
  -- so d is between b and e ⟹ ∠a:b:e = ∠a:b:d = ∠b:a:e.
  rcases hside with hon | hss
  · exfalso; euclid_finish
  · euclid_apply (proposition_32 b a d c AB AC DB)
    have hgopp : g.opposingSides b AC := by euclid_finish
    have hnbtw : ¬ between e a g := by euclid_finish
    have heopp : e.opposingSides b AC := by euclid_finish
    have hbde : between b d e := by euclid_finish
    euclid_finish

end Elements.Book3
