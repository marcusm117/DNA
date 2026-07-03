import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- ∠d:c:b = ∠d:c:a + ∠a:c:b from sum_angles_onlyif at vertex C (interior = a)
theorem helper_1_7_step5_c2_sumc (a b c d : Point) (AB AC CB AD DB CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hcCB : c.onLine CB) (hbCB : b.onLine CB) (hcb : c ≠ b)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (had : a ≠ d)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (hdb : d ≠ b)
    (hsameSide : c.sameSide d AB) (hcd : c ≠ d)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hlen : |(a─c)| = |(a─d)|) (hlen2 : |(c─b)| = |(d─b)|)
    (step4 : ∠ a:c:d = ∠ a:d:c)
    (h1 : a.sameSide b CD) (h2 : ¬d.sameSide b AC)
    : ∠ d:c:b = ∠ d:c:a + ∠ a:c:b := by
  euclid_apply (sum_angles_onlyif c d b a CD CB)
  euclid_finish

end Elements.Book1
