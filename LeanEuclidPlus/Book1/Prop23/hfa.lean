import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_23_hfa (a f : Point) (AB : Line)
    (ha_AB : a.onLine AB) (hfoff : ¬f.onLine AB)
    : f ≠ a := by
  euclid_finish

end Elements.Book1
