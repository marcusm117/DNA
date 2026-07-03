import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step5 (a b c d e f g : Point) (AB AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (habd : between a b d) (hbfd : between b f d)
    (hace : between a c e) (hage : between a g e) :
    (∠ f:a:c = ∠ f:a:g) ∧ (∠ g:a:b = ∠ f:a:g) := by
  constructor <;> euclid_finish

end Elements.Book1
