import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_3_step1 (a d c₀ c₁ : Point)
    (had : |(a─d)| = |(c₀─c₁)|) : |(a─d)| = |(c₀─c₁)| := by
  exact had

end Elements.Book1
