import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: b.sameSide c HF. b and c both lie on AB, which is parallel to HF (¬HF.intersectsLine
   AB) and distinct from it. Both are off HF, so two points on AB lie on the same side of HF. -/
theorem helper_2_7_step3_bchk (b c : Point) (AB HF : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hABHF : AB ≠ HF) (hHFAB : ¬(HF.intersectsLine AB)) :
    b.sameSide c HF := by
  euclid_intros
  have hboff : ¬(b.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point b HF AB); euclid_finish
  have hcoff : ¬(c.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point c HF AB); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing b c HF AB)
  euclid_apply (intersection_symm HF AB)
  euclid_finish

end Elements.Book2
