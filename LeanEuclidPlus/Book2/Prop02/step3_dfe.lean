import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.3: the foot f of the middle vertical CF on the bottom line DE keeps the top
   order between a c b, giving between d f e. CF ∥ AD given; AD ∥ BE from the square; CF ∥ BE via
   proposition_30. (Isolated so the area split in step3 gets the betweenness cheaply.) -/
theorem helper_2_2_step3_dfe (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hdAD : d.onLine AD) (haAD : a.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (hdsaBE : d.sameSide a BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) :
    between d f e := by
  euclid_intros
  euclid_apply (proposition_30 CF BE AD)
  euclid_finish

end Elements.Book2
