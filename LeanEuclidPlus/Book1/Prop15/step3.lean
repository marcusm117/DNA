import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_15_step3
  (c e a d : Point)
  (hstep1 : ∠ c:e:a + ∠ a:e:d = ∟ + ∟)
  : ∠ c:e:a + ∠ a:e:d = ∟ + ∟ := by
  exact hstep1

end Elements.Book1
