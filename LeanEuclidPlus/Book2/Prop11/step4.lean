import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_11_step4
    (a c f0 : Point) (AC : Line)
    (hbet : between c a f0) (hf0AC : f0.onLine AC) :
    between c a f0 ∧ f0.onLine AC := by
  exact ⟨hbet, hf0AC⟩

end Elements.Book2
