import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: a ∉ HK. a ∈ AB, which is parallel to HK (¬HK.intersectsLine AB) and distinct from it
   (g ∈ HK but g ∉ AB). A common point a of AB and HK would make them intersect. -/
theorem helper_2_4_step22_anhk (a g : Point) (AB HK : Line)
    (haAB : a.onLine AB) (hgHK : g.onLine HK) (hgnAB : ¬(g.onLine AB))
    (hHKAB : ¬(HK.intersectsLine AB)) :
    ¬(a.onLine HK) := by
  intro haHK
  have hne : HK ≠ AB := fun h => hgnAB (h ▸ hgHK)
  euclid_apply (intersection_lines_common_point a HK AB)
  euclid_finish

end Elements.Book2
