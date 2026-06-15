import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: b.sameSide a DE. b and a both lie on AB, which is parallel to DE (¬DE.intersectsLine
   AB) and distinct from it. Both are off DE, so two points on AB lie on the same side of DE. -/
theorem helper_2_4_step25_bchk2 (b a : Point) (AB DE : Line)
    (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (hABDE : AB ≠ DE) (hDEAB : ¬(DE.intersectsLine AB)) :
    b.sameSide a DE := by
  euclid_intros
  have hboff : ¬(b.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point b DE AB); euclid_finish
  have haoff : ¬(a.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point a DE AB); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing b a DE AB)
  euclid_apply (intersection_symm DE AB)
  euclid_finish

end Elements.Book2
