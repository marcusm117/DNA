import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_8_step9
  (AB AC DE DF : Line)
  (lineImg : Line → Line)
  (step8 : ¬ (lineImg AB ≠ DE) ∧ ¬ (lineImg AC ≠ DF))
  : lineImg AB = DE ∧ lineImg AC = DF :=
  ⟨Classical.not_not.mp step8.1, Classical.not_not.mp step8.2⟩

end Elements.Book1
