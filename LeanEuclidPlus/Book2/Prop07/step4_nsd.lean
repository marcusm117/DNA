import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4 sub-sub: n.sameSide d HF. n and d both lie on DE, which is parallel to HF
   (¬HF.intersectsLine DE) and distinct from it. Both are off HF, so two points on DE lie on the
   same side of HF. -/
theorem helper_2_7_step4_nsd (n d : Point) (DE HF : Line)
    (hnDE : n.onLine DE) (hdDE : d.onLine DE)
    (hHFDE : HF ≠ DE) (hHFDEni : ¬(HF.intersectsLine DE)) :
    n.sameSide d HF := by
  euclid_intros
  have hDEHF : DE ≠ HF := fun h => hHFDE h.symm
  have hnoff : ¬(n.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point n HF DE); euclid_finish
  have hdoff : ¬(d.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point d HF DE); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing n d HF DE)
  euclid_apply (intersection_symm HF DE)
  euclid_finish

end Elements.Book2
