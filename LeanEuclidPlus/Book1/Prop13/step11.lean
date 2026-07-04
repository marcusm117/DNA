import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_13_step11
    (step3 : ∠ c:b:e = ∟ ∧ ∠ e:b:d = ∟) :
    ∠ c:b:e + ∠ e:b:d = ∟ + ∟ := by
  linarith [step3.1, step3.2]

end Elements.Book1
