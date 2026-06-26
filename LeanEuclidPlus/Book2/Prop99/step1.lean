import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_99_step1 (a c e : Point) :
    |(a─c)| = |(a─c)| ∧ |(c─e)| = |(c─e)| :=
  ⟨rfl, rfl⟩

end Elements.Book2
