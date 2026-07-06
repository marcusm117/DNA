import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_34_step15
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
  (hstep3 : formTriangle a b c AB BC AC ∧ formTriangle b c d BC CD BD)
  (hstep5 : |(a─b)| = |(c─d)|)
  (hstep7 : ∠ b:a:c = ∠ c:d:b)
  (hstep12 : |(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)|)
  (hstep14 : |(a─c)| = |(d─b)|)
  : Triangle.area △ a:b:c = Triangle.area △ b:c:d := by
  euclid_apply (proposition_4 a b c d c b AB BC AC CD BC BD)
  euclid_finish

end Elements.Book1
