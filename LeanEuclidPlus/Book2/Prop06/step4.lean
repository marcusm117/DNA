import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.4: KM drawn through H parallel to AB or EF [Prop.~1.31]. Both facts (h on KM, KM ∥ AB)
   are produced by the proposition_31 construction in Main; this helper repackages them. -/
theorem helper_2_6_step4 (h : Point) (KM AB : Line)
    (hhKM : h.onLine KM) (hKMAB : ¬(KM.intersectsLine AB)) :
    h.onLine KM ∧ ¬(KM.intersectsLine AB) := by
  exact ⟨hhKM, hKMAB⟩

end Elements.Book2
