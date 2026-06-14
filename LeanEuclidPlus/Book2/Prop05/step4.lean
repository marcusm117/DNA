import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.4: KM drawn through H parallel to AB/EF [Prop.~1.31]. The line KM through h, parallel to AB,
   is produced by the proposition_31 construction in Main; this helper repackages its facts. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step4 (h : Point) (KM AB : Line)
    (hhKM : h.onLine KM) (hKMAB : ¬(KM.intersectsLine AB)) :
    h.onLine KM ∧ ¬(KM.intersectsLine AB) := by
  exact ⟨hhKM, hKMAB⟩

end Elements.Book2
