import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step5
  (g b : Point) (EF : Line)
  (hBD : ¬g.sameSide b EF)
  : ¬g.sameSide b EF :=
  hBD

end Elements.Book1
