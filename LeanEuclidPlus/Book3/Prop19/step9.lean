import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_19_step9 (f : Point) (CA : Line)
    (habsurd1 : ¬(¬f.onLine CA)) : f.onLine CA := by
  by_contra h
  exact habsurd1 h

end Elements.Book3
