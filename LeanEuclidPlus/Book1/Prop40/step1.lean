import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_40_step1 (a d : Point) (AD : Line)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (had : a ≠ d) :
    distinctPointsOnLine a d AD := by
  exact ⟨haAD, hdAD, had⟩

end Elements.Book1
