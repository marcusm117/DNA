import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step23 (b e : Point) (AC DB : Line)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC) :
    b.sameSide e AC := by
  euclid_finish

end Elements.Book3
