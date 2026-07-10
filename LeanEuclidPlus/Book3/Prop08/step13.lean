import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step13 (k g m d : Point)
    (hbetdgm : between d g m)
    (hassump1 : |(m─k)| + |(k─d)| > |(m─d)|)
    (hassump2 : |(m─g)| = |(m─k)|) :
    |(d─k)| > |(d─g)| := by
  euclid_finish

end Elements.Book3
