import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step10
    (a b e f : Point) (AB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB) (heAB : ¬e.onLine AB)
    (hbet : between a f b)
    (hassump1 : ∠ a:f:e = ∟)
    : ∠ a:f:e = ∠ b:f:e := by
  have hperp2 : ∠ b:f:e = ∟ := by euclid_finish
  exact hassump1.trans hperp2.symm

end Elements.Book3
