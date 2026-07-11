import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_22_step1 (a b c d : Point) (AC BD : Line)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
  (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hbd : b ≠ d) :
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD := by
  euclid_finish

end Elements.Book3
