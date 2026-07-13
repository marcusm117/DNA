import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step18 (b e : Point) (AC : Line)
    (hassump1 : e.opposingSides b AC) :
    e.opposingSides b AC := by
  exact hassump1

end Elements.Book3
