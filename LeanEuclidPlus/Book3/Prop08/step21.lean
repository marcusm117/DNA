import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- "DL than DH": restates step18.
theorem helper_3_8_step21
    (step18 : |(d─l)| < |(d─h)|) :
    |(d─l)| < |(d─h)| := by
  assumption

end Elements.Book3
