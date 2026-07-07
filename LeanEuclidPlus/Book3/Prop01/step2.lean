import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step2 (a b d : Point)
    (h_bet : between a d b) (h_eq : |(a─d)| = |(d─b)|) :
    between a d b ∧ |(a─d)| = |(d─b)| := by
  exact ⟨h_bet, h_eq⟩

end Elements.Book3
