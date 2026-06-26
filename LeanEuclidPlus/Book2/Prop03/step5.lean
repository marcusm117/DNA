import SystemE
import Book.Prop30
import Book2.Prop03.step5_edf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.3.5: AE is the rectangle contained by AB and BC. AE is contained by AB and BE, and BE = BC.
   With between e d f (step5_edf), the corner f of the whole rectangle b a e f sits so ∠b:e:f =
   ∠b:e:d = ∟; rectangle_area gives △b:a:e + △b:f:e = |b─a|*|b─e|, and |b─e| = |c─b| = |b─c|. -/
theorem helper_2_3_step5 (a b c d e f : Point) (AB DE CD BE AF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hfDE : f.onLine DE) (heDE : e.onLine DE) (hdDE : d.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hbe : |(b─e)| = |(c─b)|) (hbed : ∠ b:e:d = ∟)
    (hdscBE : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE))
    (hAFCD : ¬(AF.intersectsLine CD)) (heb : e ≠ b) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)| := by
  euclid_intros
  have step5_edf : between e d f := by euclid_apply (helper_2_3_step5_edf a b c d e f AB DE CD BE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)))
  euclid_apply (proposition_30 AF BE CD)
  euclid_apply (rectangle_area b a e f AB DE BE AF)
  have hba : |(a─b)| = |(b─a)| := by euclid_finish
  have hbc : |(b─c)| = |(b─e)| := by euclid_finish
  have hprod : |(a─b)| * |(b─c)| = |(b─a)| * |(b─e)| := by rw [hba, hbc]
  rw [hprod]
  euclid_finish

end Elements.Book2
