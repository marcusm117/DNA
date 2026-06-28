import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step15_qhoe_ss (e o q : Point)
    (EF OP : Line)
    (h_e_ef : e.onLine EF)
    (h_q_op : q.onLine OP) (h_o_op : o.onLine OP)
    (h_efop : ¬(EF.intersectsLine OP)) (h_eoffop : ¬(e.onLine OP)) :
    q.sameSide o EF := by
  have hne_op_ef : OP ≠ EF := fun heq => h_eoffop (heq ▸ h_e_ef)
  euclid_apply (Elements.sameSide_of_parallel_both q o OP EF)
  euclid_finish

end Elements.Book2
