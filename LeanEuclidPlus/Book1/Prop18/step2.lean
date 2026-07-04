import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_18_step2 (a b c d : Point) (AB BC AC BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hbetween : between a d c)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    : distinctPointsOnLine b d BD := by
  refine ⟨hbBD, hdBD, ?_⟩
  euclid_finish

end Elements.Book1
