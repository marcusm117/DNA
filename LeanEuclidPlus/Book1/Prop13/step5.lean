import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_13_step5
    (step4 : ∠ c:b:e + ∠ e:b:d = ∠ c:b:a + ∠ a:b:e + ∠ e:b:d) :
    ∠ c:b:e + ∠ e:b:d = ∠ c:b:a + ∠ a:b:e + ∠ e:b:d := by
  exact step4

end Elements.Book1
