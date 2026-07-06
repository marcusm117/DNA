import SystemE
import Book1.Prop16.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step3 (a b c d : Point) (AB BC AC BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hassump1 : between a d c)
    : ∠ a:d:b > ∠ d:c:b := by
  have hnbAC : ¬b.onLine AC := by euclid_finish
  have hcda : between c d a := (between_symm a d c hassump1).1
  euclid_apply (proposition_16 b c d a BC AC BD)
  have h_sym : ∠ a:d:b = ∠ b:d:a := by euclid_finish
  linarith

end Elements.Book1
