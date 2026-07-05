import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_39_step8
    (a b c d e : Point) (AB BC AC BD CD AD AE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (habne : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hdBD : d.onLine BD) (hbBD : b.onLine BD) (hdbne : d ≠ b)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hBDBC : BD ≠ BC) (hBCCD : BC ≠ CD) (hCDBD : CD ≠ BD)
    (heBD : e.onLine BD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (haADne : a ≠ d)
    (haAE : a.onLine AE) (heAE : e.onLine AE)
    (hassumpAE : ¬AE.intersectsLine BC)
    (hADmeets : AD.intersectsLine BC)
    (hasdBC : a.sameSide d BC)
    (step6 : Triangle.area △ a:b:c = Triangle.area △ d:b:c)
    : Triangle.area △ d:b:c ≠ Triangle.area △ e:b:c := by
  have step8_dne : d ≠ e := by
    intro hde; subst hde
    have hADeqAE : AD = AE := by euclid_finish
    exact hassumpAE (hADeqAE ▸ hADmeets)
  intro heq
  euclid_finish

end Elements.Book1
