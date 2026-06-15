import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: g ∉ BE. g lies on CF, which is parallel to BE (¬CF.intersectsLine BE) and distinct
   from it. A common point g of CF and BE would make them intersect. -/
theorem helper_2_4_step25_gnbe (g : Point) (CF BE : Line)
    (hgCF : g.onLine CF) (hCFBE : CF ≠ BE) (hCFBE' : ¬(CF.intersectsLine BE)) :
    ¬(g.onLine BE) := by
  intro hgBE
  euclid_apply (intersection_lines_common_point g CF BE)
  euclid_finish

end Elements.Book2
