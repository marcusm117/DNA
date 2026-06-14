import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.15 sub: b ∉ HK. b lies on AB, which is parallel to HK (¬HK.intersectsLine AB) and distinct
   from it (g ∈ HK but g ∉ AB). A common point b of HK and AB would make them intersect. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step15_bnhk (b g : Point) (AB HK : Line)
    (hbAB : b.onLine AB) (hgHK : g.onLine HK) (hgnAB : ¬(g.onLine AB))
    (hHKAB : ¬(HK.intersectsLine AB)) :
    ¬(b.onLine HK) := by
  intro hbHK
  have hne : HK ≠ AB := fun h => hgnAB (h ▸ hgHK)
  euclid_apply (intersection_lines_common_point b HK AB)
  euclid_finish

end Elements.Book2
