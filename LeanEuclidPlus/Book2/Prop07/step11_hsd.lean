import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.11 sub: h.sameSide d CN. h and d both lie on AD, which is parallel to CN (¬AD.intersectsLine
   CN) and distinct from it. Both are off CN, so two points on AD lie on the same side of CN. -/
theorem helper_2_7_step11_hsd (h d : Point) (AD CN : Line)
    (hhAD : h.onLine AD) (hdAD : d.onLine AD)
    (hADCN : AD ≠ CN) (hCNADni : ¬(CN.intersectsLine AD)) :
    h.sameSide d CN := by
  euclid_intros
  have hADCNni : ¬(AD.intersectsLine CN) := by
    intro hh; euclid_apply (intersection_symm AD CN); euclid_finish
  have hhoff : ¬(h.onLine CN) := by
    intro hon; euclid_apply (intersection_lines_common_point h CN AD); euclid_finish
  have hdoff : ¬(d.onLine CN) := by
    intro hon; euclid_apply (intersection_lines_common_point d CN AD); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing h d CN AD)
  euclid_apply (intersection_symm CN AD)
  euclid_finish

end Elements.Book2
