import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- The external-touch supposition (two contact points d, b, with h outside ABDC).
theorem helper_3_13_step13 (ABDC : Circle) (d b h : Point)
    (hsuppose2 : d ≠ b ∧ h.outsideCircle ABDC) :
    d ≠ b ∧ h.outsideCircle ABDC := hsuppose2

end Elements.Book3
