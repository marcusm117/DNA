import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_22_step1 (d e : Point) (DE : Line)
    (hd : d.onLine DE) (he : e.onLine DE)
    (hbet : between d e''' e) : distinctPointsOnLine d e DE := by
  euclid_finish

end Elements.Book1
