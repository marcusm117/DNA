import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- "And it was shown that neither (does it) internally" — this is step11.
theorem helper_3_13_step19 (ABDC : Circle) (d b h : Point)
    (step11 : ¬(d ≠ b ∧ h.insideCircle ABDC)) :
    ¬(d ≠ b ∧ h.insideCircle ABDC) := step11

end Elements.Book3
