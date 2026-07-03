import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_10_step2 (a b c d d' : Point) (AB AC BC CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC)
    (hcCD : c.onLine CD) (hd'CD : d'.onLine CD) (hdCD : d.onLine CD)
    (hd'sAC : d'.sameSide b AC) (hd'sBC : d'.sameSide a BC)
    (hbis : ∠ a:c:d' = ∠ b:c:d') :
    ∠ a:c:d = ∠ b:c:d := by
  euclid_finish

end Elements.Book1
