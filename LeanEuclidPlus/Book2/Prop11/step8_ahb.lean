import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_11_step8_ahb
    (a b c e f f0 h : Point) (AB AC AH : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hbet_aec : between a e c)
    (hac_ab : |(a─c)| = |(a─b)|)
    (hbet_caf0 : between c a f0)
    (hbet_eff0 : between e f f0)
    (hah_af : |(a─h)| = |(a─f)|)
    (hhAH : h.onLine AH) (haAH : a.onLine AH)
    (hang_fah : ∠ f:a:h = ∟)
    (hang_bac : ∠ b:a:c = ∟) :
    |(a─b)| = |(a─h)| + |(b─h)| := by
  euclid_finish

end Elements.Book2
