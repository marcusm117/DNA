import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_16_step13 (a b c d e f : Point) (AC BC : Line)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_BC_ne_AC : BC ≠ AC)
    (h_aec : between a e c) (h_bcd : between b c d)
    (h_step11 : ∠ b:a:e = ∠ e:c:f)
    (h_step12 : ∠ e:c:d > ∠ e:c:f) :
    ∠ a:c:d > ∠ b:a:e := by
  have h_e_AC : e.onLine AC := by
    euclid_apply (between_same_line_in a e c AC); assumption
  euclid_finish

end Elements.Book1
