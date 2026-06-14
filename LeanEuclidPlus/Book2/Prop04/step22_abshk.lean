import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: a.sameSide b HK. a and b both lie on AB, which is parallel to HK (¬HK.intersectsLine
   AB) and distinct from it. Both are off HK, so two points on AB lie on the same side of HK. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step22_abshk (a b : Point) (AB HK : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hABHK : AB ≠ HK) (hHKAB : ¬(HK.intersectsLine AB)) :
    a.sameSide b HK := by
  euclid_intros
  have haoff : ¬(a.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point a HK AB); euclid_finish
  have hboff : ¬(b.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point b HK AB); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing a b HK AB)
  euclid_apply (intersection_symm HK AB)
  euclid_finish

end Elements.Book2
