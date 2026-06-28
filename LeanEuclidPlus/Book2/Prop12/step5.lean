import SystemE
import Book.Prop47
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_2_12_step5
  (a b c d : Point) (AB BC CA : Line)
  (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcCA : c.onLine CA) (haCA : a.onLine CA)
  (hABBC : AB ≠ BC) (hBCCA : BC ≠ CA) (hCAAB : CA ≠ AB)
  (hdCA : d.onLine CA) (hbet : between d a c)
  (hassump1 : ∠ b:d:c = ∟)
  : |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| := by
  euclid_apply (line_from_points b d) as BD
  euclid_apply (proposition_47 d a b CA AB BD)
  euclid_finish

end Elements.Book2
