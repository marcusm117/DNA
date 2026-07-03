import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_3_step5 (a d e c₀ c₁ : Point)
    (hstep3 : |(a─e)| = |(a─d)|) (hstep4 : |(c₀─c₁)| = |(a─d)|) :
    |(a─e)| = |(a─d)| ∧ |(c₀─c₁)| = |(a─d)| := by
  exact ⟨hstep3, hstep4⟩

end Elements.Book1
