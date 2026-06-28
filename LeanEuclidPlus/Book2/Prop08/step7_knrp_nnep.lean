import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step7_knrp_nnep (k n p : Point) (MN OP : Line)
    (h_k_mn : k.onLine MN) (h_n_mn : n.onLine MN) (h_p_op : p.onLine OP)
    (h_k_off_op : ¬(k.onLine OP)) (h_mn_op : ¬(MN.intersectsLine OP)) :
    n ≠ p := by
  have hne_mn_op : MN ≠ OP := fun heq => h_k_off_op (heq ▸ h_k_mn)
  have h_n_off_op : ¬(n.onLine OP) := by
    euclid_apply (Elements.offLine_of_parallel_simple n MN OP)
    euclid_finish
  intro hnp
  exact h_n_off_op (hnp ▸ h_p_op)

end Elements.Book2
