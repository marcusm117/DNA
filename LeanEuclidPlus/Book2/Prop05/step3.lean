import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.3: DG drawn through D parallel to CE/BF [Prop.~1.31]. The line DG through d, parallel to CE,
   is produced by the proposition_31 construction in Main; this helper repackages its facts. -/
theorem helper_2_5_step3 (d : Point) (DG CE : Line)
    (hdDG : d.onLine DG) (hDGCE : ¬(DG.intersectsLine CE)) :
    d.onLine DG ∧ ¬(DG.intersectsLine CE) := by
  exact ⟨hdDG, hDGCE⟩

end Elements.Book2
