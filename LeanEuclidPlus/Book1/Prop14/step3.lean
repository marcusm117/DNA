import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_14_step3 (a b c d : Point)
  (h : ∠ a:b:c + ∠ a:b:d = ∟ + ∟) : ∠ a:b:c + ∠ a:b:d = ∟ + ∟ := by
  exact h

end Elements.Book1
