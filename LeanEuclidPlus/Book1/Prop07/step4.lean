import SystemE
import Book.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_7_step4 (a c d : Point) (AB AC CD AD : Line)
    (haAB : a.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hcd : c ≠ d)
    (hsameSide : c.sameSide d AB)
    (hlen : |(a─c)| = |(a─d)|) : ∠ a:c:d = ∠ a:d:c := by
  euclid_apply (proposition_5' a c d AC CD AD)
  euclid_finish

end Elements.Book1
