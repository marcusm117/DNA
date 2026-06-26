import SystemE
import Book2.Prop04.step5_collin
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.5 sub: c is not on AD. If c ∈ AD then a, c are two distinct shared points of AB and AD ⟹
   AB = AD, placing a, b, d collinear on AD; but then ∠ b:a:d ≠ ∟ (step5_collin), contradicting
   the square's right angle. -/
theorem helper_2_4_step5_cnad (a b c d : Point) (AB AD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hab : a ≠ b) (had : a ≠ d)
    (hbad : ∠ b:a:d = ∟) :
    ¬(c.onLine AD) := by
  intro hcAD
  euclid_apply (between_same_line_in a c b AB)
  have hABAD : AB = AD := by
    euclid_apply (two_points_determine_line a c AB AD)
    euclid_finish
  rw [hABAD] at hbAB
  have step5_collin : ∠ b:a:d ≠ ∟ := by euclid_apply (helper_2_4_step5_collin a b c d AD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)))
  exact step5_collin hbad

end Elements.Book2
