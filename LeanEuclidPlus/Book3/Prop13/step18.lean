import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- The external reductio (habsurd2) is exactly this conclusion.
theorem helper_3_13_step18 (ABDC : Circle) (d b h : Point)
    (habsurd2 : ¬(d ≠ b ∧ h.outsideCircle ABDC)) :
    ¬(d ≠ b ∧ h.outsideCircle ABDC) := habsurd2

end Elements.Book3
