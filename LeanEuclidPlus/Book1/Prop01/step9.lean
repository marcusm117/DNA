import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_1_step9 (a b c : Point)
    (h7 : |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|)
    (h8 : (|(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|) → |(c─a)| = |(c─b)|) :
    |(c─a)| = |(c─b)| := by
  exact h8 h7

end Elements.Book1
