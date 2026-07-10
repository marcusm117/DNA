import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- "DL than DH": restates step18.
set_option systemE.solverTime 30 in
theorem helper_3_8_step21
    (step18 : |(d─l)| < |(d─h)|) :
    |(d─l)| < |(d─h)| := by
  assumption

end Elements.Book3
