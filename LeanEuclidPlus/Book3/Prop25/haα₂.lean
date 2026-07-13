import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_haα₂ (a : Point) (α₂ : Circle)
    (ha_circ : a.onCircle α₂) :
    a.onCircle α₂ := by
  exact ha_circ

end Elements.Book3
