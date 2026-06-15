import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4 sub: c.sameSide b DE. c and b both lie on AB, which is parallel to DE (¬AB.intersectsLine
   DE) and distinct from it. Both are off DE, so two points on AB lie on the same side of DE. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step4_cbde (c b : Point) (AB DE : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hABDE : AB ≠ DE) (hABDEni : ¬(AB.intersectsLine DE)) :
    c.sameSide b DE := by
  euclid_intros
  have hcoff : ¬(c.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point c DE AB); euclid_finish
  have hboff : ¬(b.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point b DE AB); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing c b DE AB)
  euclid_apply (intersection_symm DE AB)
  euclid_finish

end Elements.Book2
