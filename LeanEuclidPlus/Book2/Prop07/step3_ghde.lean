import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: g.sameSide h DE. g and h both lie on HF, which is parallel to DE (¬DE.intersectsLine
   HF) and distinct from it. Both are off DE, so two points on HF lie on the same side of DE. -/
theorem helper_2_7_step3_ghde (g h : Point) (HF DE : Line)
    (hgHF : g.onLine HF) (hhHF : h.onLine HF)
    (hHFDE : HF ≠ DE) (hHFDEni : ¬(HF.intersectsLine DE)) :
    g.sameSide h DE := by
  euclid_intros
  have hDEHF : ¬(DE.intersectsLine HF) := by
    intro hh; euclid_apply (intersection_symm DE HF); euclid_finish
  have hgoff : ¬(g.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point g DE HF); euclid_finish
  have hhoff : ¬(h.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point h DE HF); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing g h DE HF)
  euclid_apply (intersection_symm DE HF)
  euclid_finish

end Elements.Book2
