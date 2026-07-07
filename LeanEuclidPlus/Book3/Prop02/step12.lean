import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step12 (d f p : Point)
    (hbet : between d f p)
    (hstep11 : |(d─f)| > |(d─p)|) :
    False := by
  euclid_finish

end Elements.Book3
