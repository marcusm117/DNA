import SystemE
import Book2.Prop06.step2_eoff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.2: DE joined. line_from_points d e in Main puts d, e on DE; d ≠ e because e is off the
   base line AB (square corner: ∠d:c:e = ∟ would degenerate if c,d,e collinear) while d ∈ AB. -/
theorem helper_2_6_step2 (a b c d e : Point) (AB DE : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟) :
    distinctPointsOnLine d e DE := by
  have step2_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_6_step2_eoff a b c d e AB (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  euclid_finish

end Elements.Book2
