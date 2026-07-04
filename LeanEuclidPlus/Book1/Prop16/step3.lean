import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_16_step3 (b e f : Point)
    (h_eq : |(e─f)| = |(b─e)|) :
    |(e─f)| = |(b─e)| :=
  h_eq

end Elements.Book1
