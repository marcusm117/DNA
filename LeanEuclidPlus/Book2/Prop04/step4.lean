import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.4: HK drawn through G parallel to AB/DE [Prop.~1.31]. The line HK through g, parallel to
   AB, is produced by the proposition_31 construction in Main; this helper repackages its facts. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step4 (g : Point) (HK AB : Line)
    (hgHK : g.onLine HK) (hHKAB : ¬(HK.intersectsLine AB)) :
    g.onLine HK ∧ ¬(HK.intersectsLine AB) := by
  exact ⟨hgHK, hHKAB⟩

end Elements.Book2
