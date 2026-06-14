import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.31 sub: f.sameSide d HK. f and d both lie on DE, which is parallel to HK (¬HK.intersectsLine
   DE) and distinct from it. Both are off HK, so two points on DE lie on the same side of HK. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step31_fsd (f d : Point) (DE HK : Line)
    (hfDE : f.onLine DE) (hdDE : d.onLine DE)
    (hDEHK : DE ≠ HK) (hHKDE : ¬(HK.intersectsLine DE)) :
    f.sameSide d HK := by
  euclid_intros
  have hfoff : ¬(f.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point f HK DE); euclid_finish
  have hdoff : ¬(d.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point d HK DE); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing f d HK DE)
  euclid_apply (intersection_symm HK DE)
  euclid_finish

end Elements.Book2
