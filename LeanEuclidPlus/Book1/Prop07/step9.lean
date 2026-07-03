import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- False from step7 (= equal) and step8 (> greater): direct arithmetic contradiction
theorem helper_1_7_step9 (c d b : Point)
    (step7 : ∠ c:d:b = ∠ d:c:b)
    (step8 : ∠ c:d:b > ∠ d:c:b)
    : False := by linarith

end Elements.Book1
