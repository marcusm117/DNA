import SystemE
import Book2.Prop03.step7_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.3.7: DB is the square on CB. The square CDEB (formParallelogram d e c b DE AB CD BE = step6_hsq)
   with right angle ∠e:c:d... apply rectangle_area to it; its area = |c─d|*|c─e|-style product, and
   the edges |c─d| = |c─b| = |b─c|, |c─e| (= the other side) likewise, giving |b─c|*|b─c|. -/
theorem helper_2_3_step7 (a b c d e : Point) (AB DE CD BE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hcd : |(c─d)| = |(c─b)|) (hde : |(d─e)| = |(c─b)|) (hbe : |(b─e)| = |(c─b)|)
    (hbcd : ∠ b:c:d = ∟) (hcde : ∠ c:d:e = ∟) (hcbe : ∠ c:b:e = ∟) (hbed : ∠ b:e:d = ∟)
    (hdscBE : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE)) :
    Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)| := by
  euclid_intros
  have step7_par : formParallelogram c b d e AB DE CD BE := by euclid_apply (helper_2_3_step7_par a b c d e AB DE CD BE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(b─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CD.intersectsLine BE); assumption)))
  euclid_apply (rectangle_area c b d e AB DE CD BE)
  have hcb : |(c─b)| = |(b─c)| := by euclid_finish
  have hcd2 : |(c─d)| = |(b─c)| := by euclid_finish
  have hprod : |(b─c)| * |(b─c)| = |(c─b)| * |(c─d)| := by rw [hcb, hcd2]
  rw [hprod]
  euclid_finish

end Elements.Book2
