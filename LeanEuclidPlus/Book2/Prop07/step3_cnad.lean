import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: c is not on AD. If c ∈ AD then a, c are two distinct shared points of AB and AD ⟹
   AB = AD, placing a, b, d collinear on AD; but then ∠ b:a:d ≠ ∟ (step3_collin), contradicting
   the square's right angle. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_cnad (a b c d : Point) (AB AD : Line)
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
  have step3_collin : ∠ b:a:d ≠ ∟ := by sorry
  exact step3_collin hbad

end Elements.Book2
