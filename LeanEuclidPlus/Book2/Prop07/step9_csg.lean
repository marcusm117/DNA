import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.9 sub: c.sameSide g BE. c and g both lie on CN, which is parallel to BE (¬CN.intersectsLine
   BE) and distinct from it. Both are off BE, so two points on CN lie on the same side of BE. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step9_csg (c g : Point) (CN BE : Line)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (hCNBE : CN ≠ BE) (hCNBEni : ¬(CN.intersectsLine BE)) :
    c.sameSide g BE := by
  euclid_intros
  have hcoff : ¬(c.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point c BE CN); euclid_finish
  have hgoff : ¬(g.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point g BE CN); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing c g BE CN)
  euclid_apply (intersection_symm BE CN)
  euclid_finish

end Elements.Book2
