import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_2_step11 (a l b c g : Point)
    (h1 : |(a─l)| = |(b─g)|) (h2 : |(b─c)| = |(b─g)|) :
    |(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)| := by
  exact ⟨h1, h2⟩

end Elements.Book1
