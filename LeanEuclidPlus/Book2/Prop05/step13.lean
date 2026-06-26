import SystemE
import Book2.Prop05.step13_dhdb
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.13: |DH| = |DB|. Triangle DHB is right-isosceles (the diagonal BE of square CEFB cuts off a
   45° angle), so DH = DB. The whole argument lives in the shared worker step13_dhdb (reused by
   step12), passed in here as a have. -/
theorem helper_2_5_step13 (b c d e h : Point) (AB CE DG BE : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hbBE : b.onLine BE) (hhBE : h.onLine BE) (heBE : e.onLine BE)
    (hbe : b ≠ e)
    (hce_cb : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟)
    (hcdb : between c d b)
    (hDGCE : ¬(DG.intersectsLine CE)) :
    |(d─h)| = |(d─b)| := by
  have step13_dhdb : |(d─h)| = |(d─b)| := by euclid_apply (helper_2_5_step13_dhdb b c d e h AB CE DG BE (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
  exact step13_dhdb

end Elements.Book2
