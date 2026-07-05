import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_39_step3 (a : Point) (AE BC : Line)
    (h1 : a.onLine AE) (h2 : ¬AE.intersectsLine BC) :
    a.onLine AE ∧ ¬AE.intersectsLine BC :=
  ⟨h1, h2⟩

end Elements.Book1
