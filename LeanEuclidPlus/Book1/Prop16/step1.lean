import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_16_step1 (a e c : Point)
    (h_btwn : between a e c) (h_eq : |(a─e)| = |(e─c)|) :
    between a e c ∧ |(a─e)| = |(e─c)| := by
  exact ⟨h_btwn, h_eq⟩

end Elements.Book1
