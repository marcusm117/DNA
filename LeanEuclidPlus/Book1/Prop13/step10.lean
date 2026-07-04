import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_13_step10
    (step7 : ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c)
    (step8 : ∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c)
    (step9 : (∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) →
             (∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) →
             (∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c)) :
    ∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c := by
  exact step9 step8 step7

end Elements.Book1
