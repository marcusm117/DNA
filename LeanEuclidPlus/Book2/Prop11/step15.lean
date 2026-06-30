import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step15
    (a b c f : Point)
    (hstep14 : |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)|) :
    |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)| := by
  exact hstep14

end Elements.Book2
