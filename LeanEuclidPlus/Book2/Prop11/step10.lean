import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step10
    (b e f : Point)
    (hef_be : |(e─f)| = |(b─e)|) :
    |(e─f)| = |(e─b)| := by
  euclid_finish

end Elements.Book2
