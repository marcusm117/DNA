import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_hoffBD_nbet
    (a b c d : Point) (BC BD : Line)
    (hab : a ≠ b)
    (h : a.onLine BD) (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (h_cbd : (∠ c:b:d : ℝ) = ∟)
    (hbet : ¬between a b d)
    (hacute : (∠ a:b:c : ℝ) < ∟) :
    False := by
  euclid_apply (equal_angles b a d c c BD BC)
  euclid_finish

end Elements.Book1
