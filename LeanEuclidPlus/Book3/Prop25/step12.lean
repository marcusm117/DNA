import SystemE
import Book1.Prop04.Main
import Book3.Prop25.step12_eoff
import Book3.Prop25.step12_tri1
import Book3.Prop25.step12_tri2

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step12 (a b c d e g : Point) (AC DB AB AG EC : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c) (hb_off : ¬b.onLine AC)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB) (he_db : e.onLine DB)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (ha_ag : a.onLine AG) (hg_ag : g.onLine AG) (he_ag : e.onLine AG) (hg_ne : g ≠ a)
    (he_ec : e.onLine EC) (hc_ec : c.onLine EC)
    (hside : g.onLine AB ∨ g.sameSide d AB)
    (hang : ∠ g:a:b = ∠ a:b:d) (hgt : ∠ a:b:d > ∠ b:a:d) (hright : ∠ a:d:b = ∟)
    (hstep10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|) (hstep11 : ∠ a:d:e = ∠ c:d:e) :
    |(a─e)| = |(c─e)| := by
  have step12_eoff : ¬ e.onLine AC := by euclid_apply (helper_3_25_step12_eoff a b c d e g AC DB AB AG (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g.onLine AB ∨ g.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)))
  have step12_tri1 : formTriangle d a e AC AG DB := by euclid_apply (helper_3_25_step12_tri1 a c d e AC AG DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ¬ e.onLine AC; assumption)))
  have step12_tri2 : formTriangle d c e AC EC DB := by euclid_apply (helper_3_25_step12_tri2 a c d e AC EC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ¬ e.onLine AC; assumption)))
  euclid_apply (proposition_4 d a e d c e AC AG DB AC EC DB)
  euclid_finish

end Elements.Book3
