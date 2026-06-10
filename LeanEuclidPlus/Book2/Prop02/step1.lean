import SystemE
import Book.Prop30

namespace Elements.Book2

open Elements.Book1

/- 2.2.1 (construction): square ADEB on AB, CF through C parallel to AD/BE, f = CF ∩ DE.
   The crux `between d f e` follows from `between a c b` and the parallel verticals
   (CF ∥ AD given, CF ∥ BE via proposition_30). -/
set_option systemE.solverTime 30 in
theorem helper_2_step1 (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hab : distinctPointsOnLine a b AB) (hc : c.onLine AB) (hacb : between a c b)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hde : |(d─e)| = |(a─b)|) (had : |(a─d)| = |(a─b)|) (hbe : |(b─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (hade : ∠ a:d:e = ∟) (habe : ∠ a:b:e = ∟) (hbed : ∠ b:e:d = ∟)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD))
    (hfDE : f.onLine DE) (hfCF : f.onLine CF) :
    |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
    (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧
    c.onLine CF ∧ ¬(CF.intersectsLine AD) ∧
    f.onLine DE ∧ f.onLine CF ∧ between d f e := by
  euclid_intros
  euclid_apply (proposition_30 CF BE AD)
  euclid_finish

end Elements.Book2
