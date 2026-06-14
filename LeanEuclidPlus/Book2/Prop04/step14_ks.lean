import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.14 sub: k.sameSide g AB. Both k and g lie on HK, which is parallel to AB
   (¬HK.intersectsLine AB) and distinct from it (g ∉ AB). Two points on a line parallel and distinct
   from AB are on the same side of AB. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step14_ks (g k : Point) (AB HK : Line)
    (hgHK : g.onLine HK) (hkHK : k.onLine HK) (hgnAB : ¬(g.onLine AB))
    (hHKAB : ¬(HK.intersectsLine AB)) :
    k.sameSide g AB := by
  euclid_intros
  have hkoff : ¬(k.onLine AB) := by
    intro hon
    have hne : HK ≠ AB := fun h => hgnAB (h ▸ hgHK)
    euclid_apply (intersection_lines_common_point k HK AB)
    euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing k g AB HK)
  euclid_apply (intersection_symm AB HK)
  euclid_finish

end Elements.Book2
