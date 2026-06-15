import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.31 sub: c.sameSide b HK. c and b both lie on AB, which is parallel to HK (¬HK.intersectsLine
   AB) and distinct from it. Both are off HK, so two points on AB lie on the same side of HK. -/
theorem helper_2_4_step31_csb (c b : Point) (AB HK : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hABHK : AB ≠ HK) (hHKAB : ¬(HK.intersectsLine AB)) :
    c.sameSide b HK := by
  euclid_intros
  have hcoff : ¬(c.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point c HK AB); euclid_finish
  have hboff : ¬(b.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point b HK AB); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing c b HK AB)
  euclid_apply (intersection_symm HK AB)
  euclid_finish

end Elements.Book2
