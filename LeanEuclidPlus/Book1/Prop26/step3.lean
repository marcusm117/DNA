import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step3
    (b g d e c : Point)
    (hassump1 : |(b─g)| = |(d─e)|)
    (hassump2 : |(b─c)| = |(e─f)|) :
    |(g─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| := by
  exact ⟨by euclid_finish, hassump2⟩

end Elements.Book1
