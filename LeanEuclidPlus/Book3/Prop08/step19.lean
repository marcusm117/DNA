import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- "DG is the least": just restates step14 (GD < KD proved there).
set_option systemE.solverTime 30 in
theorem helper_3_8_step19
    (step14 : |(d─g)| < |(d─k)|) :
    |(d─g)| < |(d─k)| := by
  assumption

end Elements.Book3
