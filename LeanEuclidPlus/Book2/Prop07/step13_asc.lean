import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: a.sameSide c DE. a and c both lie on AB, which is parallel to DE (¬AB.intersectsLine
   DE) and distinct from it. Both are off DE, so two points on AB lie on the same side of DE. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_asc (a c : Point) (AB DE : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (hABDE : AB ≠ DE) (hABDEni : ¬(AB.intersectsLine DE)) :
    a.sameSide c DE := by
  euclid_intros
  have haoff : ¬(a.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point a DE AB); euclid_finish
  have hcoff : ¬(c.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point c DE AB); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing a c DE AB)
  euclid_apply (intersection_symm DE AB)
  euclid_finish

end Elements.Book2
