import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.8 sub: a.sameSide b HF. a and b both lie on AB, which is parallel to HF (¬HF.intersectsLine
   AB) and distinct from it. Both are off HF, so two points on AB lie on the same side of HF. -/
theorem helper_2_7_step8_abhf (a b : Point) (AB HF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hABHF : AB ≠ HF) (hHFAB : ¬(HF.intersectsLine AB)) :
    a.sameSide b HF := by
  euclid_intros
  have haoff : ¬(a.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point a HF AB); euclid_finish
  have hboff : ¬(b.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point b HF AB); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing a b HF AB)
  euclid_apply (intersection_symm HF AB)
  euclid_finish

end Elements.Book2
