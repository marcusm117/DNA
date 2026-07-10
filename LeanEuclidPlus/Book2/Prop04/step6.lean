import SystemE
import Book1Variants.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.6: ∠ a:d:b = ∠ a:b:d. Triangle a,d,b is isosceles with |a─d| = |a─b| (the square's two sides
   from a), so its base angles at d and b are equal [Prop.~1.5]. The triangle is formed by AD (a,d),
   BD (b,d) and AB (a,b); ∠ b:a:d = ∟ guarantees the three vertices are non-collinear. -/
theorem helper_2_4_step6 (a b d : Point) (AB AD BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hab : a ≠ b) (hbd : b ≠ d)
    (hadab : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟) :
    ∠ a:d:b = ∠ a:b:d := by
  euclid_intros
  euclid_apply (proposition_5' a d b AD BD AB)
  euclid_finish

end Elements.Book2
