import SystemE
import Book.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- ∠b:d:c = ∠b:c:d from proposition_5' on triangle BDC with |b─d| = |b─c|
theorem helper_1_7_step5_c2_iso (a b c d : Point) (AB AC CB AD DB CD : Line)
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
    : ∠ b:d:c = ∠ b:c:d := by
  euclid_apply (proposition_5' b d c DB CD CB)
  euclid_finish

end Elements.Book1
