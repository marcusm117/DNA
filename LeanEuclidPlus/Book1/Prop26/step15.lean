import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step15
    (hstep13 : |(a─b)| = |(d─e)|)
    (hstep14 : |(b─c)| = |(e─f)|) :
    |(a─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| :=
  ⟨hstep13, hstep14⟩

end Elements.Book1
