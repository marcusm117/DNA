import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_16_step4 (a b c e f : Point) (AC BC AB BE FC : Line)
    (h_f_FC : f.onLine FC) (h_c_FC : c.onLine FC)
    (h_b_BE : b.onLine BE) (h_e_BE : e.onLine BE)
    (h_bef : between b e f)
    (h_aec : between a e c)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_BC_ne_AC : BC ≠ AC) :
    distinctPointsOnLine f c FC := by
  refine ⟨h_f_FC, h_c_FC, ?_⟩
  euclid_finish

end Elements.Book1
