import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_21_step1 (a b c d e : Point) (AB BC AC BD DC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (heBD : e.onLine BD) (heAC : e.onLine AC)
    (hbdAC : b.sameSide d AC) (hadBC : a.sameSide d BC) (hcdAB : c.sameSide d AB) :
    between b d e ∧ e.onLine BD := by
  constructor
  · euclid_finish
  · exact heBD

end Elements.Book1
