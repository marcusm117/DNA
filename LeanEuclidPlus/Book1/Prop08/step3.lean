import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_8_step3
  (AB BC AC DE EF DF : Line)
  (lineImg : Line → Line)
  (hassump1 : lineImg BC = EF)
  (hne : lineImg AB ≠ DE ∧ lineImg AC ≠ DF)
  : lineImg AB ≠ DE ∧ lineImg AC ≠ DF :=
  hne

end Elements.Book1
