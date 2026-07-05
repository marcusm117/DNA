import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_33_step1
  (a b c : Point) (AC BD BC : Line)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_b_BD : b.onLine BD)
  (h_a_side_c : a.sameSide c BD)
  (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC) (h_ac : a ≠ c)
  : distinctPointsOnLine b c BC := by
  euclid_finish

end Elements.Book1
