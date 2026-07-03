import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_2_step1 (a b : Point) (AB : Line)
    (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b) :
    distinctPointsOnLine a b AB := by
  euclid_finish

end Elements.Book1
