import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step4 (d g m a e : Point)
    (hbetdgm : between d g m) (hbetgma : between g m a)
    (hstep3 : |(m─a)| + |(m─d)| = |(e─m)| + |(m─d)|) :
    |(d─a)| = |(e─m)| + |(m─d)| := by
  euclid_finish

end Elements.Book3
