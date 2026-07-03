import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_8_step8
  (AB AC DE DF : Line)
  (lineImg : Line → Line)
  (step2 : lineImg AB = DE ∧ lineImg AC = DF)
  : ¬ (lineImg AB ≠ DE) ∧ ¬ (lineImg AC ≠ DF) :=
  ⟨fun h => h step2.1, fun h => h step2.2⟩

end Elements.Book1
