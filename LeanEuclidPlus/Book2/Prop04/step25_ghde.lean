import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: g.sameSide h DE. g and h both lie on HK, which is parallel to DE (¬DE.intersectsLine
   HK) and distinct from it. Both are off DE, so two points on HK lie on the same side of DE. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step25_ghde (g h : Point) (HK DE : Line)
    (hgHK : g.onLine HK) (hhHK : h.onLine HK)
    (hHKDE : HK ≠ DE) (hDEHK : ¬(DE.intersectsLine HK)) :
    g.sameSide h DE := by
  euclid_intros
  have hgoff : ¬(g.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point g DE HK); euclid_finish
  have hhoff : ¬(h.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point h DE HK); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing g h DE HK)
  euclid_apply (intersection_symm DE HK)
  euclid_finish

end Elements.Book2
