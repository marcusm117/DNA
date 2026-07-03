import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_2_step10 (b c g : Point)
    (h1 : |(b─c)| = |(b─g)|) :
    |(b─c)| = |(b─g)| := by
  exact h1

end Elements.Book1
