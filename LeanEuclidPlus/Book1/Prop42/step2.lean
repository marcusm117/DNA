import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step2 (a b c e : Point) (AB BC AE : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_AB_ne_BC : AB ≠ BC)
    (h_bet : between b e c)
    (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) :
    distinctPointsOnLine a e AE := by
  euclid_finish

end Elements.Book1
