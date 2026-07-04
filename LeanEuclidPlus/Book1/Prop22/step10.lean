import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_22_step10 (f d a a' : Point) (h : |(d─f)| = |(a─a')|) :
    |(f─d)| = |(a─a')| := by
  euclid_finish

end Elements.Book1
