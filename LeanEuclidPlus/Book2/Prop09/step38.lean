import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_9_step38
  (b d f : Point)
  (hstep18 : |(f─d)| = |(d─b)|) :
  |(d─f)| = |(d─b)| := by
  euclid_finish

end Elements.Book2
