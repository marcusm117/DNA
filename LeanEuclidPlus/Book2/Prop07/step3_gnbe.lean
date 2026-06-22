import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: g ∉ BE. g lies on CN, which is parallel to BE (¬CN.intersectsLine BE) and distinct
   from it. A common point g of CN and BE would make them intersect. -/
theorem helper_2_7_step3_gnbe (g : Point) (CN BE : Line)
    (hgCN : g.onLine CN) (hCNBE : CN ≠ BE) (hCNBE' : ¬(CN.intersectsLine BE)) :
    ¬(g.onLine BE) := by
  intro hgBE
  euclid_apply (intersection_lines_common_point g CN BE)
  euclid_finish

end Elements.Book2
