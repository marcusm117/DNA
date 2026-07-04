import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_16_step6 (a b c e f : Point)
    (hassump1 : |(a─e)| = |(e─c)|)
    (hassump2 : |(b─e)| = |(e─f)|) :
    |(a─e)| = |(c─e)| ∧ |(b─e)| = |(e─f)| := by
  exact ⟨by euclid_finish, hassump2⟩

end Elements.Book1
