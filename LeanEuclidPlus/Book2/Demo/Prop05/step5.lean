import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.5: AK drawn through A parallel to CL/BM (i.e. CE) [Prop.~1.31]. The line AK through a,
   parallel to CE, is produced by the proposition_31 construction in Main; this helper repackages. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step5 (a : Point) (AK CE : Line)
    (haAK : a.onLine AK) (hAKCE : ¬(AK.intersectsLine CE)) :
    a.onLine AK ∧ ¬(AK.intersectsLine CE) := by
  exact ⟨haAK, hAKCE⟩

end Elements.Book2
