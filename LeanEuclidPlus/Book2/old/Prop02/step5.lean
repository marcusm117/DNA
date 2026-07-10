import SystemE
import Book1.Prop30.Main

namespace Elements.Book2

open Elements.Book1

/- 2.2.5: CE = rect(AB,BC). rectangle_area on the sub-rectangle b,c,f,e; |b─e| = |a─b|. -/
set_option systemE.solverTime 30 in
theorem helper_2_2_step5 (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hbe : |(b─e)| = |(a─b)|) (habe : ∠ a:b:e = ∟)
    (hcAB : c.onLine AB) (hacb : between a c b)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD))
    (hfDE : f.onLine DE) (hfCF : f.onLine CF) (hdfe : between d f e) :
    Triangle.area △ f:c:b + Triangle.area △ f:b:e = |(a─b)| * |(b─c)| := by
  euclid_intros
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (rectangle_area b c e f AB DE BE CF)
  have hab : |(a─b)| = |(b─e)| := by euclid_finish
  have hprod : |(a─b)| * |(b─c)| = |(b─e)| * |(b─c)| := by rw [hab]
  rw [hprod]
  euclid_finish

end Elements.Book2
