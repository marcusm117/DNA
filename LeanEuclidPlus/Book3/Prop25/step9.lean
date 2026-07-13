import SystemE
import Book1.Prop06.Main
import Book3.Prop25.step9_htri

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step9 (a b c d e g : Point) (AC AG AB DB : Line)
    (ha_ag : a.onLine AG) (he_ag : e.onLine AG) (hg_ag : g.onLine AG) (hg_ne : g ≠ a)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (hb_db : b.onLine DB) (he_db : e.onLine DB)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c)
    (hd_db : d.onLine DB) (hb_off : ¬b.onLine AC)
    (hside : g.onLine AB ∨ g.sameSide d AB)
    (hang : ∠ g:a:b = ∠ a:b:d) (hgt : ∠ a:b:d > ∠ b:a:d)
    (hangeq : ∠ a:b:e = ∠ b:a:e) :
    |(e─b)| = |(e─a)| := by
  have step9_htri : formTriangle e a b AG AB DB := by euclid_apply (helper_3_25_step9_htri a b c d e g AC AG AB DB (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine AB ∨ g.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)))
  euclid_apply (proposition_6 e a b AG AB DB)
  euclid_finish

end Elements.Book3
