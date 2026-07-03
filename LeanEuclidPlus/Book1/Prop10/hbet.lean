import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_10_hbet (a b c d d' : Point) (AB AC BC CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hd'CD : d'.onLine CD)
    (hdAB : d.onLine AB)
    (hd'sAC : d'.sameSide b AC) (hd'sBC : d'.sameSide a BC)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (hca : |(c─a)| = |(a─b)|) (hcb : |(c─b)| = |(a─b)|)
    (hstep6 : |(a─d)| = |(d─b)|) :
    between a d b := by
  euclid_finish

end Elements.Book1
