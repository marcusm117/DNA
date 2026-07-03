import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_9_hfa (a f : Point) (AF : Line)
    (h : distinctPointsOnLine a f AF) : f ≠ a :=
  fun heq => h.2.2 heq.symm

end Elements.Book1
