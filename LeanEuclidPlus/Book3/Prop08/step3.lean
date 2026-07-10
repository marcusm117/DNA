import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step3
  (hassump1 : |(m─a)| = |(m─e)|)
  : |(m─a)| + |(m─d)| = |(e─m)| + |(m─d)| := by
  euclid_finish

end Elements.Book3
