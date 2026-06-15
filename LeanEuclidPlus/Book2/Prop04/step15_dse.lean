import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.15 sub-sub: d.sameSide e HK. d and e both lie on DE, which is parallel to HK
   (¬DE.intersectsLine HK) and distinct from it. Both are off HK (a shared point would make DE meet
   HK, as DE ≠ HK), and two points on a line parallel to HK lie on the same side of HK. -/
theorem helper_2_4_step15_dse (d e : Point) (DE HK : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hDEHKne : DE ≠ HK) (hDEHK : ¬(DE.intersectsLine HK)) :
    d.sameSide e HK := by
  euclid_intros
  have hdoff : ¬(d.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point d DE HK); euclid_finish
  have heoff : ¬(e.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point e DE HK); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing d e HK DE)
  euclid_apply (intersection_symm HK DE)
  euclid_finish

end Elements.Book2
