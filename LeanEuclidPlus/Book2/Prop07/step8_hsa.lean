import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.8 sub: h.sameSide a BE. h and a both lie on AD, which is parallel to BE (¬AD.intersectsLine
   BE) and distinct from it. Both are off BE, so two points on AD lie on the same side of BE. -/
theorem helper_2_7_step8_hsa (h a : Point) (AD BE : Line)
    (hhAD : h.onLine AD) (haAD : a.onLine AD)
    (hADBE : AD ≠ BE) (hADBEni : ¬(AD.intersectsLine BE)) :
    h.sameSide a BE := by
  euclid_intros
  have hhoff : ¬(h.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point h BE AD); euclid_finish
  have haoff : ¬(a.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point a BE AD); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing h a BE AD)
  euclid_apply (intersection_symm BE AD)
  euclid_finish

end Elements.Book2
