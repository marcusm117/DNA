import SystemE
import Book.Prop13
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_14_step2
  (a b c e : Point) (AB BC : Line)
  (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab_ne : a ≠ b)
  (hb_bc : b.onLine BC) (hc_bc : c.onLine BC)
  (he_bc : e.onLine BC) (hc_ab : ¬c.onLine AB)
  (hcbe : between c b e)   -- "since the straight-line $AB$ stands on the straight-line $CBE$"
  : ∠ a:b:c + ∠ a:b:e = ∟ + ∟ := by
  euclid_apply (proposition_13 a b e c AB BC)
  euclid_finish

end Elements.Book1
