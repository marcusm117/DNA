import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step6_ebc (b e c : Point) (BC : Line)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_bet : between b e c) :
    e.onLine BC := by
  euclid_finish

end Elements.Book1
