import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.3: BG drawn through B parallel to EC or DF [Prop.~1.31]. Both facts (b on BG, BG ∥ CE)
   are produced by the proposition_31 construction in Main; this helper repackages them. -/
theorem helper_2_6_step3 (b : Point) (BG CE : Line)
    (hbBG : b.onLine BG) (hBGCE : ¬(BG.intersectsLine CE)) :
    b.onLine BG ∧ ¬(BG.intersectsLine CE) := by
  exact ⟨hbBG, hBGCE⟩

end Elements.Book2
