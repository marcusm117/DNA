import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

-- step5 (2.13.5): square on AC = squares on AD and DC [Prop.~1.47].
-- Pythagoras on right triangle d–a–c (right angle ∠a:d:c=∟ given directly).
-- proposition_47 (d a c DA CA BC) has conclusion = this claim exactly.
theorem helper_2_13_step5
  (a b c d : Point) (AB BC CA : Line)
  (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcCA : c.onLine CA) (haCA : a.onLine CA)
  (hABBC : AB ≠ BC) (hBCCA : BC ≠ CA) (hCAAB : CA ≠ AB)
  (hdBC : d.onLine BC) (hbet : between b d c)
  (hrt : ∠ a:d:c = ∟)
  : |(a─c)| * |(a─c)| = |(a─d)| * |(a─d)| + |(d─c)| * |(d─c)| := by
  euclid_apply (line_from_points d a) as DA
  euclid_apply (proposition_47 d a c DA CA BC)
  euclid_finish

end Elements.Book2
