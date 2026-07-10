import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step5
  (hassump1 : |(e─b)| = |(e─c)|)
  (hassump2 : |(f─e)| = |(f─e)|)
  : |(e─b)| = |(e─c)| ∧ |(e─f)| = |(e─f)| := by
  exact ⟨hassump1, rfl⟩

end Elements.Book3
