import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: g ≠ f. g lies on HK, which is parallel to DE (¬HK.intersectsLine DE) and distinct from
   it; so g ∉ DE. But f ∈ DE, hence g ≠ f. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step22_gf (g f : Point) (HK DE : Line)
    (hgHK : g.onLine HK) (hfDE : f.onLine DE)
    (hHKDE : HK ≠ DE) (hHKDE' : ¬(HK.intersectsLine DE)) :
    g ≠ f := by
  have hgnDE : ¬(g.onLine DE) := by
    intro hgDE; euclid_apply (intersection_lines_common_point g HK DE); euclid_finish
  intro hgf
  rw [hgf] at hgnDE
  exact hgnDE hfDE

end Elements.Book2
