import SystemE
import Book1.Prop06.Main
import Book3.Prop25.hEb_ang
import Book3.Prop25.hEb_tri

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hEb (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c) (hb_off : ¬b.onLine AC)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB) (he_db : e.onLine DB)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (ha_ag3 : a.onLine AG3) (hg3_ag3 : g3.onLine AG3) (he_ag3 : e.onLine AG3) (hg3_ne : g3 ≠ a)
    (hside : g3.onLine AB ∨ g3.sameSide d AB)
    (hang : ∠ g3:a:b = ∠ a:b:d) (hright : ∠ a:d:b = ∟)
    (hlt : ∠ a:b:d < ∠ b:a:d)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC) :
    |(e─a)| = |(e─b)| := by
  have hEb_ang : ∠ a:b:e = ∠ b:a:e := by euclid_apply (helper_3_25_hEb_ang a b c d e g3 AC DB AB AG3 (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d < ∠ b:a:d; assumption)) (by euclid_assumption "" (show e.onLine DB ∧ e.sameSide b AC; assumption)))
  have hEb_tri : formTriangle e a b AG3 AB DB := by euclid_apply (helper_3_25_hEb_tri a b c d e g3 AC AG3 AB DB (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:b:d < ∠ b:a:d; assumption)))
  euclid_apply (proposition_6 e a b AG3 AB DB)
  euclid_finish

end Elements.Book3
