import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_39_step5_sideEC
    (e c : Point) (AB : Line)
    (h : e.sameSide c AB)
    : e.sameSide c AB :=
  h

end Elements.Book1
