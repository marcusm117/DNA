import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: a.sameSide h CN. a and h both lie on AD, which is parallel to CN (¬CN.intersectsLine
   AD) and distinct from it. Both are off CN, so two points on AD lie on the same side of CN. -/
theorem helper_2_7_step3_ahcf (a h : Point) (AD CN : Line)
    (haAD : a.onLine AD) (hhAD : h.onLine AD)
    (hADCN : AD ≠ CN) (hCNAD : ¬(CN.intersectsLine AD)) :
    a.sameSide h CN := by
  euclid_intros
  have haoff : ¬(a.onLine CN) := by
    intro hon; euclid_apply (intersection_lines_common_point a CN AD); euclid_finish
  have hhoff : ¬(h.onLine CN) := by
    intro hon; euclid_apply (intersection_lines_common_point h CN AD); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing a h CN AD)
  euclid_apply (intersection_symm CN AD)
  euclid_finish

end Elements.Book2
