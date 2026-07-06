import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_33_step4
  (a b c d : Point) (AB CD AC BD BC : Line)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab : a ≠ b)
  (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD) (h_cd : c ≠ d)
  (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC) (h_ac : a ≠ c)
  (h_b_BD : b.onLine BD) (h_d_BD : d.onLine BD) (h_bd : b ≠ d)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_same : a.sameSide c BD)
  (h_par : ¬(AB.intersectsLine CD))
  (h_len : |(a─b)| = |(c─d)|)
  (step2 : ∠ a:b:c = ∠ b:c:d)
  : |(a─c)| = |(b─d)| := by
  euclid_apply (proposition_4 c b d b c a BC BD CD BC AC AB)
  euclid_finish

end Elements.Book1
