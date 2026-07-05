import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- TODO: fill object/hypothesis binders (run --context step3)
theorem helper_1_34_step3
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
  (hassump1 : ∠ a:b:c = ∠ b:c:d ∧ ∠ b:c:a = ∠ c:b:d)
  : formTriangle a b c AB BC AC ∧ formTriangle b c d BC CD BD := by
  constructor <;> euclid_finish

end Elements.Book1
