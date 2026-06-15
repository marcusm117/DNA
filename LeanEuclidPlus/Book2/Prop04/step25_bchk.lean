import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: b.sameSide c HK. b and c both lie on AB, which is parallel to HK (¬HK.intersectsLine
   AB) and distinct from it. Both are off HK, so two points on AB lie on the same side of HK. -/
theorem helper_2_4_step25_bchk (b c : Point) (AB HK : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hABHK : AB ≠ HK) (hHKAB : ¬(HK.intersectsLine AB)) :
    b.sameSide c HK := by
  euclid_intros
  have hboff : ¬(b.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point b HK AB); euclid_finish
  have hcoff : ¬(c.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point c HK AB); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing b c HK AB)
  euclid_apply (intersection_symm HK AB)
  euclid_finish

end Elements.Book2
