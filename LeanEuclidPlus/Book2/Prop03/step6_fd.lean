import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact: f ≠ d. between e d f makes d strictly between e and f, so f ≠ d. -/
theorem helper_2_3_step6_fd (d e f : Point) (hedf : between e d f) : f ≠ d := by
  euclid_finish

end Elements.Book2
