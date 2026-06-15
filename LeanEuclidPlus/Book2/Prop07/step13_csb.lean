import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: c.sameSide b HF. c and b both lie on AB, which is parallel to HF (¬HF.intersectsLine
   AB) and distinct from it. Both are off HF, so two points on AB lie on the same side of HF. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_csb (c b : Point) (AB HF : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hABHF : AB ≠ HF) (hHFAB : ¬(HF.intersectsLine AB)) :
    c.sameSide b HF := by
  euclid_intros
  have hcoff : ¬(c.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point c HF AB); euclid_finish
  have hboff : ¬(b.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point b HF AB); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing c b HF AB)
  euclid_apply (intersection_symm HF AB)
  euclid_finish

end Elements.Book2
