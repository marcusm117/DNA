import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step21 (a c d : Point) (α₂ : Circle)
    (hbet : between a d c) (hcentre : d.isCentre α₂) :
    between a d c ∧ d.isCentre α₂ := by
  exact ⟨hbet, hcentre⟩

end Elements.Book3
