import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step8_gkqr_kner (k r : Point) (OP : Line)
    (h_r_op : r.onLine OP) (h_k_off_op : ¬(k.onLine OP)) :
    k ≠ r := by
  intro hkr
  exact h_k_off_op (hkr ▸ h_r_op)

end Elements.Book2
