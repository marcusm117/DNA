import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- step8 recalls step6: "But it was shown that the former (angle) is also much greater"
theorem helper_1_7_step8 (c d b : Point)
    (step6 : ∠ c:d:b > ∠ d:c:b)
    : ∠ c:d:b > ∠ d:c:b := step6

end Elements.Book1
