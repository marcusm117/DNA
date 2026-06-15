import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: a.sameSide h CF. a and h both lie on AD, which is parallel to CF (¬CF.intersectsLine
   AD) and distinct from it. Both are off CF (a shared point would make AD meet CF), so two points on
   AD lie on the same side of CF. -/
theorem helper_2_4_step22_ahcf (a h : Point) (AD CF : Line)
    (haAD : a.onLine AD) (hhAD : h.onLine AD)
    (hADCF : AD ≠ CF) (hCFAD : ¬(CF.intersectsLine AD)) :
    a.sameSide h CF := by
  euclid_intros
  have haoff : ¬(a.onLine CF) := by
    intro hon; euclid_apply (intersection_lines_common_point a CF AD); euclid_finish
  have hhoff : ¬(h.onLine CF) := by
    intro hon; euclid_apply (intersection_lines_common_point h CF AD); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing a h CF AD)
  euclid_apply (intersection_symm CF AD)
  euclid_finish

end Elements.Book2
