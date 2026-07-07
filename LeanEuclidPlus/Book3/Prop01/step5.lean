import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step5 (c e f : Point)
    (h_bet : between c f e) (h_eq : |(c─f)| = |(f─e)|) :
    between c f e ∧ |(c─f)| = |(f─e)| := by
  exact ⟨h_bet, h_eq⟩

end Elements.Book3
