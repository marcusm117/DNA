import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step24_efopp (a b c d e f : Point) (AB CH : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_c_ch : c.onLine CH)
    (h_each : e.sameSide a CH) (h_fdch : f.sameSide d CH) :
    ¬(e.sameSide f CH) := by
  have h_acd : between a c d := by
    euclid_finish
  euclid_apply (pasch_3 a c d CH)
  euclid_finish

end Elements.Book2
