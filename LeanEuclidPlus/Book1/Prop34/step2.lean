import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_34_step2
  (a b c d : Point) (AB CD AC BD BC : Line)
  (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
  (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
  (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
  (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
  (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
  (hbd : b ≠ d) (hbc : b ≠ c)
  (hsameside : a.sameSide c BD)
  (hpar1 : ¬(AB.intersectsLine CD))
  (hassump1 : ¬(AC.intersectsLine BD))
  (hassump2 : c.onLine AC ∧ c.onLine BC ∧ b.onLine BD ∧ b.onLine BC)
  : ∠ a:c:b = ∠ c:b:d := by
  euclid_apply (proposition_29''' a d c b AC BD BC)
  euclid_finish

end Elements.Book1
