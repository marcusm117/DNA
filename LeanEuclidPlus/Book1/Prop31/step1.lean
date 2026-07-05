import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_31_step1 (d : Point) (BC : Line)
    (hd : d.onLine BC) : d.onLine BC := by
  exact hd

end Elements.Book1
