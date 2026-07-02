import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_14_step6 (a b d e : Point)
  (h5 : ∠ a:b:e = ∠ a:b:d) : ∠ a:b:e = ∠ a:b:d := by
  exact h5

end Elements.Book1
