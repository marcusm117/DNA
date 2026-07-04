import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_16_step12 (a b c d e f : Point) (AB BC AC BE FC : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
    (h_b_BE : b.onLine BE) (h_e_BE : e.onLine BE)
    (h_f_FC : f.onLine FC) (h_c_FC : c.onLine FC)
    (h_bcd : between b c d) (h_aec : between a e c)
    (h_bef : between b e f)
    (h_ang : ∠ a:e:b = ∠ f:e:c)
    (h_step11 : ∠ b:a:e = ∠ e:c:f) :
    ∠ e:c:d > ∠ e:c:f := by
  euclid_finish

end Elements.Book1
