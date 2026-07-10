import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- "DK is less than DL": restates step17.
theorem helper_3_8_step20
    (step17 : |(d─k)| < |(d─l)|) :
    |(d─k)| < |(d─l)| := by
  assumption

end Elements.Book3
