import SystemE
import Book.Prop47
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

-- step4 (2.13.4): square on AB = squares on BD and DA, since angle at D is right [Prop.~1.47].
-- Pythagoras on right triangle d–a–b (right angle ∠a:d:b, derived from ∠a:d:c=∟ + b,d,c collinear).
-- Construct the foot-to-apex line DA, then proposition_47 closes up to segment symmetry.
theorem helper_2_13_step4
  (a b c d : Point) (AB BC CA : Line)
  (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcCA : c.onLine CA) (haCA : a.onLine CA)
  (hABBC : AB ≠ BC) (hBCCA : BC ≠ CA) (hCAAB : CA ≠ AB)
  (hdBC : d.onLine BC) (hbet : between b d c)
  (hassump1 : ∠ a:d:c = ∟)
  : |(a─b)| * |(a─b)| = |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| := by
  euclid_apply (line_from_points d a) as DA
  euclid_apply (proposition_47 d a b DA AB BC)
  euclid_finish

end Elements.Book2
