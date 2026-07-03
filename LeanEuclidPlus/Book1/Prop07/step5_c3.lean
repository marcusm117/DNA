import SystemE
import Book.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Case 3: ¬a.sameSide b CD ∧ d.sameSide b AC → contradiction via extension points
theorem helper_1_7_step5_c3 (a b c d : Point) (AB AC CB AD DB CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hcCB : c.onLine CB) (hbCB : b.onLine CB) (hcb : c ≠ b)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (had : a ≠ d)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (hdb : d ≠ b)
    (hsameSide : c.sameSide d AB) (hcd : c ≠ d)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hlen : |(a─c)| = |(a─d)|) (hlen2 : |(c─b)| = |(d─b)|)
    (step4 : ∠ a:c:d = ∠ a:d:c)
    (h1 : ¬a.sameSide b CD) (h2 : d.sameSide b AC)
    : ∠ a:d:c > ∠ d:c:b := by
  exfalso
  euclid_apply (extend_point AC a c) as e
  euclid_apply (extend_point AD a d) as f
  euclid_apply (proposition_5 a c d e f AC CD AD)
  euclid_apply (sum_angles_onlyif c e d b AC CD)
  euclid_apply (proposition_5' b c d CB CD DB)
  euclid_apply (sum_angles_onlyif d c b f CD DB)
  euclid_finish

end Elements.Book1
