import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.5: AK drawn through A parallel to CL or DM [Prop.~1.31]. Both facts (a on AK, AK ∥ CE)
   are produced by the proposition_31 construction in Main; this helper repackages them. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step5 (a : Point) (AK CE : Line)
    (haAK : a.onLine AK) (hAKCE : ¬(AK.intersectsLine CE)) :
    a.onLine AK ∧ ¬(AK.intersectsLine CE) := by
  exact ⟨haAK, hAKCE⟩

end Elements.Book2
