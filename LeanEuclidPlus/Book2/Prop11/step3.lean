import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_11_step3
    (a b c e : Point) (AB AC BE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbet : between a e c)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hang : ∠ b:a:c = ∟) :
    distinctPointsOnLine b e BE := by
  euclid_finish

end Elements.Book2
