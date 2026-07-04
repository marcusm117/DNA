import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_23_step5 (d e f g : Point)
    (h_fg : |(f─g)| = |(e─d)|)
    : |(d─e)| = |(f─g)| := by
  euclid_finish

end Elements.Book1
