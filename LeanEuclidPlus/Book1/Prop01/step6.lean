import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_1_step6 (a b c : Point)
    (h : |(a─c)| = |(a─b)|) :
    |(c─a)| = |(a─b)| := by
  rw [segment_symmetric c a]
  exact h

end Elements.Book1
