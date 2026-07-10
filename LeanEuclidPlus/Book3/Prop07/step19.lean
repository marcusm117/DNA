import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step19
    (hassump1 : |(e─g)| = |(e─h)|)
    (hassump2 : |(e─f)| = |(e─f)|)
    : |(e─g)| = |(e─h)| ∧ |(e─f)| = |(e─f)| :=
  ⟨hassump1, hassump2⟩

end Elements.Book3
