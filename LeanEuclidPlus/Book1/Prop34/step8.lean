import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_34_step8
  (a b c d : Point) (AB CD AC BD BC : Line)
  (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
  (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
  (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
  (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
  (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
  (hbd : b ≠ d) (hbc : b ≠ c)
  (hsameside : a.sameSide c BD)
  (hpar1 : ¬(AB.intersectsLine CD))
  (hpar2 : ¬(AC.intersectsLine BD))
  (hstep1 : ∠ a:b:c = ∠ b:c:d)
  (hstep2 : ∠ a:c:b = ∠ c:b:d)
  (hassump1 : ∠ a:b:c = ∠ b:c:d)
  (hassump2 : ∠ c:b:d = ∠ a:c:b)
  : ∠ a:b:d = ∠ a:c:d := by
  euclid_finish

end Elements.Book1
