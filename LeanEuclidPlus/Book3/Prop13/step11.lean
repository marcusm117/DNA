import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- The internal reductio (habsurd1) is exactly this conclusion.
theorem helper_3_13_step11 (ABDC : Circle) (d b h : Point)
    (habsurd1 : ¬(d ≠ b ∧ h.insideCircle ABDC)) :
    ¬(d ≠ b ∧ h.insideCircle ABDC) := habsurd1

end Elements.Book3
