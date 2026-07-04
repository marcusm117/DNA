import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_13_step9 :
    (∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) →
    (∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) →
    (∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c) := by
  intro h1 h2; linarith

end Elements.Book1
