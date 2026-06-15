import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.14 sub: k ∉ AB. k lies on HK, which is parallel to AB (¬HK.intersectsLine AB) and distinct
   from it (g ∈ HK but g ∉ AB). A common point k of HK and AB would make them intersect. -/
theorem helper_2_4_step9_knab (g k : Point) (AB HK : Line)
    (hgHK : g.onLine HK) (hkHK : k.onLine HK) (hgnAB : ¬(g.onLine AB))
    (hHKAB : ¬(HK.intersectsLine AB)) :
    ¬(k.onLine AB) := by
  intro hkAB
  have hne : HK ≠ AB := fun h => hgnAB (h ▸ hgHK)
  euclid_apply (intersection_lines_common_point k HK AB)
  euclid_finish

end Elements.Book2
