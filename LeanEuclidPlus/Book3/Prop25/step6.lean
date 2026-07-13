import SystemE
import Book1.Prop32.Main

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step6 (a b c d e g : Point) (AC DB AB AG : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (hb_off : ¬b.onLine AC)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB) (he_db : e.onLine DB)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (ha_ag : a.onLine AG) (hg_ag : g.onLine AG) (he_ag : e.onLine AG) (hg_ne : g ≠ a)
    (hside : g.onLine AB ∨ g.sameSide d AB)
    (hang : ∠ g:a:b = ∠ a:b:d) (hright : ∠ a:d:b = ∟)
    (hgt : ∠ a:b:d > ∠ b:a:d) :
    ∠ b:a:e = ∠ a:b:d ∧ e ≠ a := by
  rcases hside with hon | hss
  · -- g on AB ⟹ ∠g:a:b ∈ {0, ∟+∟}, contradicting ∠g:a:b = ∠a:b:d (a proper angle)
    exfalso; euclid_finish
  · -- g on d's side of AB ⟹ e lies on the ray a→g, so ∠b:a:e = ∠b:a:g = ∠a:b:d.
    -- triangle abd sum ⟹ ∠g:a:d = ∠abd − ∠bad < ∟, so the ray a→g points toward DB (crosses at e).
    euclid_apply (proposition_32 b a d c AB AC DB)
    have hnbtw : ¬ between e a g := by euclid_finish
    euclid_finish

end Elements.Book3
