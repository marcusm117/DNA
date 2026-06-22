import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub-sub: d.sameSide e HF. d and e both lie on DE, which is parallel to HF
   (¬DE.intersectsLine HF) and distinct from it. Both are off HF, and two points on a line parallel
   to HF lie on the same side of HF. -/
theorem helper_2_7_step3_dse (d e : Point) (DE HF : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hDEHFne : DE ≠ HF) (hDEHF : ¬(DE.intersectsLine HF)) :
    d.sameSide e HF := by
  euclid_intros
  have hdoff : ¬(d.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point d DE HF); euclid_finish
  have heoff : ¬(e.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point e DE HF); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing d e HF DE)
  euclid_apply (intersection_symm HF DE)
  euclid_finish

end Elements.Book2
