import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: a.sameSide d BE. a and d both lie on AD, which is parallel to BE (¬AD.intersectsLine
   BE) and distinct from it. Both are off BE, so two points on AD lie on the same side of BE. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_asd (a d : Point) (AD BE : Line)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hADBE : AD ≠ BE) (hADBEni : ¬(AD.intersectsLine BE)) :
    a.sameSide d BE := by
  euclid_intros
  have haoff : ¬(a.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point a BE AD); euclid_finish
  have hdoff : ¬(d.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point d BE AD); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing a d BE AD)
  euclid_apply (intersection_symm BE AD)
  euclid_finish

end Elements.Book2
