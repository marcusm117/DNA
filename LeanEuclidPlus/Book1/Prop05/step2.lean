import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step2 (a e f g : Point)
    (h1 : between a g e) (h2 : |(a─g)| = |(f─a)|) :
    between a g e ∧ |(a─g)| = |(a─f)| := by
  constructor
  · exact h1
  · euclid_finish

end Elements.Book1
