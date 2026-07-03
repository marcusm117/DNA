import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_2_step13 (a l b c g : Point)
    (h11 : |(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)|)
    (h12 : (|(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)|) → |(a─l)| = |(b─c)|) :
    |(a─l)| = |(b─c)| := by
  exact h12 h11

end Elements.Book1
