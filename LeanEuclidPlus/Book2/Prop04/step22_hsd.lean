import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: h.sameSide d CF. h and d both lie on AD, which is parallel to CF (¬CF.intersectsLine
   AD) and distinct from it. Both are off CF, so two points on AD lie on the same side of CF. -/
theorem helper_2_4_step22_hsd (h d : Point) (AD CF : Line)
    (hhAD : h.onLine AD) (hdAD : d.onLine AD)
    (hADCF : AD ≠ CF) (hCFAD : ¬(CF.intersectsLine AD)) :
    h.sameSide d CF := by
  euclid_intros
  have hhoff : ¬(h.onLine CF) := by
    intro hon; euclid_apply (intersection_lines_common_point h CF AD); euclid_finish
  have hdoff : ¬(d.onLine CF) := by
    intro hon; euclid_apply (intersection_lines_common_point d CF AD); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing h d CF AD)
  euclid_apply (intersection_symm CF AD)
  euclid_finish

end Elements.Book2
