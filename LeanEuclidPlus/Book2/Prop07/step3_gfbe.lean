import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: g.sameSide n BE. g and n both lie on CN, which is parallel to BE (¬BE.intersectsLine
   CN) and distinct from it. Both are off BE, so two points on CN lie on the same side of BE. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_gfbe (g n : Point) (CN BE : Line)
    (hgCN : g.onLine CN) (hnCN : n.onLine CN)
    (hCNBE : CN ≠ BE) (hCNBEni : ¬(CN.intersectsLine BE)) :
    g.sameSide n BE := by
  euclid_intros
  have hBECN : ¬(BE.intersectsLine CN) := by
    intro hh; euclid_apply (intersection_symm BE CN); euclid_finish
  have hgoff : ¬(g.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point g BE CN); euclid_finish
  have hnoff : ¬(n.onLine BE) := by
    intro hon; euclid_apply (intersection_lines_common_point n BE CN); euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing g n BE CN)
  euclid_apply (intersection_symm BE CN)
  euclid_finish

end Elements.Book2
