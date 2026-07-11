import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_19_step8 (f : Point) (ABC : Circle) (CA : Line)
    (habsurd1 : ¬(¬f.onLine CA)) :
    ¬(f.isCentre ABC ∧ ¬f.onLine CA) :=
  fun h => habsurd1 h.2

end Elements.Book3
