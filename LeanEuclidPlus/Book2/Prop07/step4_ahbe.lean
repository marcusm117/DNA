import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4 sub: a.sameSide h BE. a and h both lie on AD, which is parallel to BE (¬AD.intersectsLine
   BE) and distinct from it. Both are off BE, so two points on AD lie on the same side of BE. -/
theorem helper_2_7_step4_ahbe (a h : Point) (AD BE : Line)
    (haAD : a.onLine AD) (hhAD : h.onLine AD)
    (hADBE : AD ≠ BE) (hADBEni : ¬(AD.intersectsLine BE)) :
    a.sameSide h BE := by
  euclid_intros
  have haoff : ¬(a.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point a BE AD); euclid_finish
  have hhoff : ¬(h.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point h BE AD); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing a h BE AD)
  euclid_apply (intersection_symm BE AD)
  euclid_finish

end Elements.Book2
