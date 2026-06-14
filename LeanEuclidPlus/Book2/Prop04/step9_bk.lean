import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.9 sub: b ≠ k. b lies on AB; k lies on HK which is parallel to AB (¬HK.intersectsLine AB), so k
   is off AB. Hence b ≠ k (a common point would put k on AB / make HK meet AB). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step9_bk (b g k : Point) (AB HK : Line)
    (hbAB : b.onLine AB) (hkHK : k.onLine HK) (hgHK : g.onLine HK) (hgAB : ¬(g.onLine AB))
    (hHKAB : ¬(HK.intersectsLine AB)) :
    b ≠ k := by
  -- HK ≠ AB since g ∈ HK but g ∉ AB
  have hne : HK ≠ AB := fun h => hgAB (h ▸ hgHK)
  intro heq
  rw [heq] at hbAB
  euclid_apply (intersection_lines_common_point k HK AB)
  euclid_finish

end Elements.Book2
