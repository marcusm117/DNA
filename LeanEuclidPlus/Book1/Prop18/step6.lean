import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step6 (a b c d : Point) (AB BC AC BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hbetween : between a d c)
    (hstep5 : ∠ a:b:d > ∠ b:c:a)
    : ∠ a:b:c > ∠ b:c:a := by
  have haSidedBC : a.sameSide d BC := by euclid_finish
  have hcSidedAB : c.sameSide d AB := by euclid_finish
  euclid_apply (sum_angles_onlyif b a c d AB BC)
  have hpos : ∠ d:b:c > 0 := by euclid_finish
  linarith

end Elements.Book1
