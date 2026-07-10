import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step6
    (hassump1 : |(m─e)| = |(m─f)|)
    (hassump2 : |(m─d)| = |(m─d)|) :
    |(e─m)| + |(m─d)| = |(f─m)| + |(m─d)| := by
  euclid_finish

end Elements.Book3
