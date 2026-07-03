import SystemE
import Book.Prop04
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_10_step6 (a b c d d' : Point) (AB AC BC CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hd'CD : d'.onLine CD)
    (hd'sAC : d'.sameSide b AC) (hd'sBC : d'.sameSide a BC)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (hca : |(c─a)| = |(a─b)|) (hcb : |(c─b)| = |(a─b)|)
    (hstep5 : ∠ a:c:d = ∠ b:c:d) :
    |(a─d)| = |(d─b)| := by
  euclid_apply (proposition_4 c a d c b d AC AB CD BC AB CD)
  euclid_finish

end Elements.Book1
