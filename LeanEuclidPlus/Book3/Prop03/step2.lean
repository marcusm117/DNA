import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step2
    (a b f e : Point)
    (hassump1 : |(a─f)| = |(f─b)|)
    (hassump2 : |(f─e)| = |(f─e)|)
    : |(a─f)| = |(f─b)| ∧ |(f─e)| = |(f─e)| := ⟨hassump1, hassump2⟩

end Elements.Book3
