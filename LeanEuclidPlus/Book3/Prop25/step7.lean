import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step7 (e : Point) (DB : Line)
    (he_db : e.onLine DB) :
    e.onLine DB := by
  exact he_db

end Elements.Book3
