import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_48_step10
    (hstep7 : |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)|)
    (hstep4 : |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|)
    (hassump_bc : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|)
    : |(d─c)| = |(b─c)| := by
  euclid_finish

end Elements.Book1
