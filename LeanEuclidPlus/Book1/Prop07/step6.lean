import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- ∠c:d:b > ∠d:c:b from step5 (∠a:d:c > ∠d:c:b) + angle containment (CDB includes ADC)
theorem helper_1_7_step6 (a b c d : Point) (AB AC CB AD DB CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hcCB : c.onLine CB) (hbCB : b.onLine CB) (hcb : c ≠ b)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (had : a ≠ d)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (hdb : d ≠ b)
    (hsameSide : c.sameSide d AB) (hcd : c ≠ d)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hlen : |(a─c)| = |(a─d)|) (hlen2 : |(c─b)| = |(d─b)|)
    (step5 : ∠ a:d:c > ∠ d:c:b)
    : ∠ c:d:b > ∠ d:c:b := by
  euclid_apply (sum_angles_onlyif d c b a CD DB)
  euclid_finish

end Elements.Book1
