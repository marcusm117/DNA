import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- sub-fact for 2.2.6: ¬(CF.intersectsLine BE). CF ∥ AD (given), AD ∥ BE (square verticals), so
   CF ∥ BE by proposition_30 (transitivity of parallelism). Rich point context lets the solver fix
   the line-distinctness preconditions of proposition_30. -/
theorem helper_2_2_step6_cfbe (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hdAD : d.onLine AD) (haAD : a.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (hdsaBE : d.sameSide a BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) :
    ¬(CF.intersectsLine BE) := by
  euclid_intros
  euclid_apply (proposition_30 CF BE AD)
  euclid_finish

end Elements.Book2
