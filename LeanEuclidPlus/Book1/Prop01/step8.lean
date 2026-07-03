import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_1_step8 (a b c : Point) :
    (|(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|) → |(c─a)| = |(c─b)| := by
  rintro ⟨h1, h2⟩
  exact h1.trans h2.symm

end Elements.Book1
