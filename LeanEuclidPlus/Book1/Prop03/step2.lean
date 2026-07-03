import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_3_step2 (a d : Point) (DEF : Circle)
    (hc : a.isCentre DEF) (hd : d.onCircle DEF) :
    a.isCentre DEF ∧ d.onCircle DEF := by
  exact ⟨hc, hd⟩

end Elements.Book1
