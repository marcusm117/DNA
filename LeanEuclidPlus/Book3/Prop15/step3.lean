import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step3
    (e h l : Point)
    (hl_eq : |(e─l)| = |(e─h)|) :
    |(e─l)| = |(e─h)| :=
  hl_eq

end Elements.Book3
