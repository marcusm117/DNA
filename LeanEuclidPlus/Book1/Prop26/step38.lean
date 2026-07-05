import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step38
    (hstep37 : |(a─b)| = |(d─e)|)
    (hstep36 : |(b─c)| = |(e─f)|) :
    |(a─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| :=
  ⟨hstep37, hstep36⟩

end Elements.Book1
